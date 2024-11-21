package main

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"log"
	"os"
	"regexp"
	"strings"

	"golang.org/x/tools/go/packages"
)

func main() {
	// Many tools pass their command-line arguments (after any flags)
	// uninterpreted to packages.Load so that it can interpret them
	// according to the conventions of the underlying build system.
	cfg := &packages.Config{Mode: packages.NeedFiles | packages.NeedSyntax | packages.NeedDeps | packages.NeedImports | packages.NeedTypesInfo}
	pkgs, err := packages.Load(cfg, "./example")
	if err != nil {
		fmt.Fprintf(os.Stderr, "load: %v\n", err)
		os.Exit(1)
	}
	if packages.PrintErrors(pkgs) > 0 {
		os.Exit(1)
	}

	jscode, err := JSify(pkgs[0])
	if err != nil {
		log.Fatalf("jsify: %s", err)
	}

	fmt.Println("JS code generated:")
	fmt.Println(jscode)
}

type NodeNotAllowedError struct {
	pos  token.Position
	node ast.Node
}

func (node NodeNotAllowedError) Error() string {
	return fmt.Sprintf("node %T at pos %s not allowed", node.node, node.pos)
}

func JSify(pkg *packages.Package) (fmt.Stringer, error) {
	for _, astFile := range pkg.Syntax {
		for _, decl := range astFile.Decls {
			funcDecl, ok := decl.(*ast.FuncDecl)
			if !ok {
				continue
			}

			if funcDecl.Recv != nil {
				continue
			}

			if funcDecl.Body == nil {
				continue
			}

			if funcDecl.Doc == nil {
				continue
			}

			funcDoc := funcDecl.Doc.List
			if len(funcDoc) != 1 {
				continue
			}

			comment := funcDoc[0]
			if comment.Text != "//go:jsify" {
				continue
			}

			js := jsifier{
				decl: funcDecl,
				pkg:  pkg,
			}
			if err := js.handleFunc(); err != nil {
				return nil, fmt.Errorf("handle func: %w", err)
			}

			return &js, nil
		}
	}

	return nil, errors.New(`directive go:jsify not found`)
}

type jsifier struct {
	buf  bytes.Buffer
	decl *ast.FuncDecl
	pkg  *packages.Package
}

func (js *jsifier) String() string {
	return js.buf.String()
}

func (js *jsifier) write(s string) {
	js.buf.WriteString(s)
}

func (js *jsifier) writeGoEnv() {
	js.write(GoEnv)
}

func (js *jsifier) handleFunc() error {
	fmt.Printf("Function %s will be jsfied\n", js.decl.Name.Name)

	js.writeGoEnv()
	return js.jsifyFuncDecl(js.decl)
}

func (js *jsifier) jsifyFuncType(node *ast.FuncType) error {
	js.write("(")

	list := node.Params
	if list == nil {
		return nil
	}
	for _, param := range list.List {
		names := param.Names
		if names == nil {
			continue
		}

		for _, name := range param.Names {
			js.write(name.Name + ", ")
		}
	}

	js.write(")")
	return nil
}

func (js *jsifier) jsifyFuncDecl(node *ast.FuncDecl) error {
	js.write("function " + node.Name.Name)

	if err := js.jsifyFuncType(node.Type); err != nil {
		return fmt.Errorf("jsify func type: %w", err)
	}

	if node.Body != nil {
		return js.jsifyStmt(node.Body)
	}

	return nil
}

func (js *jsifier) jsifyStmt(node ast.Stmt) error {
	pos := js.pkg.Fset.Position(node.Pos())

	switch node := node.(type) {
	case *ast.BlockStmt:
		return js.jsifyBlockStmt(node)
	case *ast.AssignStmt:
		return js.jsifyAssignStmt(node)
	case *ast.DeclStmt:
		return js.jsifyDeclStmt(node)
	case *ast.LabeledStmt:
		return NodeNotAllowedError{pos, node}
	case *ast.ExprStmt:
		return js.jsifyExpr(node.X)
	case *ast.SendStmt:
		panic("not implemented")
	case *ast.IncDecStmt:
		return js.jsifyIncDecStmt(node)
	case *ast.GoStmt:
		panic("not implemented")
	case *ast.DeferStmt:
		panic("not implemented")
	case *ast.ReturnStmt:
		return js.jsifyReturnStmt(node)
	case *ast.BranchStmt:
		return js.jsifyBranchStmt(node)
	case *ast.IfStmt:
		return js.jsifyIfStmt(node)
	case *ast.SwitchStmt:
		panic("not implemented")
	case *ast.TypeSwitchStmt:
		panic("not implemented")
	case *ast.SelectStmt:
		panic("not implemented")
	case *ast.ForStmt:
		panic("not implemented")
	case *ast.RangeStmt:
		panic("not implemented")
	}

	return fmt.Errorf("unknown stmt on %s", pos)
}

func (js *jsifier) jsifyBlockStmt(node *ast.BlockStmt) error {
	js.write("{\n")

	for _, stmt := range node.List {
		if stmt != nil {
			if err := js.jsifyStmt(stmt); err != nil {
				return fmt.Errorf("jsify stmt: %w", err)
			}
			js.write(";\n")
		}
	}

	js.write("}")

	return nil
}

func (js *jsifier) jsifyAssignStmt(node *ast.AssignStmt) error {
	switch node.Tok {
	case token.DEFINE:
		js.write("let ")
	}

	multiAssign := len(node.Lhs) > 1
	isCommaOk := len(node.Lhs) != len(node.Rhs) && len(node.Rhs) == 1

	var starLhs []*ast.StarExpr
	var withStarRhs []ast.Expr
	var noStartExprIds []int
	for i, expr := range node.Lhs {
		if starExpr, ok := expr.(*ast.StarExpr); ok {
			starLhs = append(starLhs, starExpr)
			withStarRhs = append(withStarRhs, node.Rhs[i])
			continue
		}

		noStartExprIds = append(noStartExprIds, i)
	}

	if len(starLhs) > 0 {
		if multiAssign {
			js.write("(")
		}

		for i := 0; i < len(starLhs); i++ {
			l, r := starLhs[i], withStarRhs[i]
			if err := js.jsifyExpr(l.X); err != nil {
				return fmt.Errorf("jsify left expr: %w", err)
			}

			js.write(".store(")

			if node.Tok != token.ASSIGN {
				if err := js.jsifyStarExpr(l); err != nil {
					return fmt.Errorf("jsify star expr: %w", err)
				}
			}

			switch node.Tok {
			case token.ADD_ASSIGN:
				js.write("+")
			case token.SUB_ASSIGN:
				js.write("-")
			case token.MUL_ASSIGN:
				js.write("*")
			case token.QUO_ASSIGN:
				js.write("/")
			case token.REM_ASSIGN:
				js.write("%")
			case token.AND_ASSIGN:
				js.write("&")
			case token.OR_ASSIGN:
				js.write("|")
			case token.XOR_ASSIGN:
				js.write("^")
			case token.SHL_ASSIGN:
				js.write("<<")
			case token.SHR_ASSIGN:
				js.write(">>")
			case token.AND_NOT_ASSIGN:
				return errors.New("and not assign (&^=) not supported")
			}

			if err := js.jsifyExpr(r); err != nil {
				return fmt.Errorf("jsify right expr: %w", err)
			}

			js.write(")")

			if i != len(starLhs)-1 {
				js.write(", ")
			}
		}

		if multiAssign {
			js.write(")")
		}
	}

	if len(noStartExprIds) == 0 {
		return nil
	} else if len(noStartExprIds) < len(node.Lhs) {
		js.write(";\n")
	}

	if multiAssign {
		js.write("[")
	}

	for i, idx := range noStartExprIds {
		expr := node.Lhs[idx]
		if err := js.jsifyExpr(expr); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}
		if i != len(noStartExprIds)-1 {
			js.write(", ")
		}
	}

	if multiAssign {
		js.write("]")
	}

	js.write(" ")

	switch node.Tok {
	case token.DEFINE, token.ASSIGN:
		js.write("=")
	case token.ADD_ASSIGN:
		js.write("+=")
	case token.SUB_ASSIGN:
		js.write("-=")
	case token.MUL_ASSIGN:
		js.write("*=")
	case token.QUO_ASSIGN:
		js.write("/=")
	case token.REM_ASSIGN:
		js.write("%=")
	case token.AND_ASSIGN:
		js.write("&=")
	case token.OR_ASSIGN:
		js.write("|=")
	case token.XOR_ASSIGN:
		js.write("^=")
	case token.SHL_ASSIGN:
		js.write("<<=")
	case token.SHR_ASSIGN:
		js.write(">>=")
	case token.AND_NOT_ASSIGN:
		return errors.New("and not assign (&^=) not supported")
		// js.write("&^=")
	default:
		panic("unreachable")
	}

	js.write(" ")

	if isCommaOk {
		js.write("Object.values(go.typeAssert(")

		if err := js.jsifyExpr(node.Rhs[0]); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}

		js.write("))")
		return nil
	}

	if multiAssign {
		js.write("[")
	}

	for i, idx := range noStartExprIds {
		expr := node.Rhs[idx]
		if err := js.jsifyExpr(expr); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}
		if i != len(noStartExprIds)-1 {
			js.write(", ")
		}
	}

	if multiAssign {
		js.write("]")
	}
	return nil
}

func (js *jsifier) jsifyDeclStmt(node *ast.DeclStmt) error {
	genDecl, ok := node.Decl.(*ast.GenDecl)
	if !ok {
		return nil
	}

	if len(genDecl.Specs) == 0 {
		return nil
	}

	switch genDecl.Tok {
	case token.CONST:
		js.write("const")
	case token.VAR:
		js.write("let")
	default:
		return nil
	}

	js.write(" [")

	for i, spec := range genDecl.Specs {
		valSpec, ok := spec.(*ast.ValueSpec)
		if !ok {
			return fmt.Errorf("expected *ast.ValueSpec, got %T", spec)
		}

		if len(valSpec.Names) == 0 {
			continue
		}

		js.write("[")
		for i, name := range valSpec.Names {
			js.write(name.Name)
			if i != len(valSpec.Names)-1 {
				js.write(", ")
			}
		}
		js.write("]")

		if i != len(genDecl.Specs)-1 {
			js.write(", ")
		}
	}

	js.write("] = [")

	for i, spec := range genDecl.Specs {
		valSpec, ok := spec.(*ast.ValueSpec)
		if !ok {
			return fmt.Errorf("expected *ast.ValueSpec, got %T", spec)
		}

		if len(valSpec.Values) == 0 {
			continue
		}

		js.write("[")
		for i, val := range valSpec.Values {
			if err := js.jsifyExpr(val); err != nil {
				return fmt.Errorf("jsify expr: %w", err)
			}
			if i != len(valSpec.Values) {
				js.write(", ")
			}
		}
		js.write("]")

		if i != len(genDecl.Specs)-1 {
			js.write(", ")
		}
	}

	js.write("]")
	return nil
}

func (js *jsifier) jsifyIncDecStmt(node *ast.IncDecStmt) error {
	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	switch node.Tok {
	case token.INC:
		js.write("++")
	case token.DEC:
		js.write("--")
	default:
		panic("unreachable")
	}

	return nil
}

func (js *jsifier) jsifyReturnStmt(node *ast.ReturnStmt) error {
	js.write("return")

	if len(node.Results) == 0 {
		return nil
	}

	js.write(" [")

	for i, res := range node.Results {
		if err := js.jsifyExpr(res); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}
		if i != len(node.Results)-1 {
			js.write(", ")
		}
	}

	js.write("]")
	return nil
}

func (js *jsifier) jsifyBranchStmt(node *ast.BranchStmt) error {
	if node.Label != nil {
		return errors.New("labels are not supported")
	}

	switch node.Tok {
	case token.BREAK:
		js.write("break")
	case token.CONTINUE:
		js.write("continue")
	case token.GOTO:
		return errors.New("goto not supported")
	case token.FALLTHROUGH:
		return errors.New("fallthrough not supported")
	default:
		panic("unreachable")
	}

	return nil
}

func (js *jsifier) jsifyIfStmt(node *ast.IfStmt) error {
	if node.Init != nil {
		js.write("{\n")
		defer js.write("}")

		if err := js.jsifyStmt(node.Init); err != nil {
			return fmt.Errorf("jsify init stmt: %w", err)
		}
	}

	js.write("if (")

	if err := js.jsifyExpr(node.Cond); err != nil {
		return fmt.Errorf("jsify cond expr: %w", err)
	}

	js.write(")")

	if err := js.jsifyBlockStmt(node.Body); err != nil {
		return fmt.Errorf("jsify body stmt: %w", err)
	}

	if node.Else != nil {
		js.write(" else ")
		if err := js.jsifyStmt(node.Else); err != nil {
			return fmt.Errorf("jsify else stmt: %w", err)
		}
	}

	return nil
}

func (js *jsifier) jsifyExpr(node ast.Expr) error {
	switch node := node.(type) {
	case *ast.Ident:
		return js.jsifyIdent(node)
	case *ast.BasicLit:
		return js.jsifyBasicLit(node)
	case *ast.FuncLit:
		return js.jsifyFuncLit(node)
	case *ast.CompositeLit:
		return js.jsifyCompositeLit(node)
	case *ast.ParenExpr:
		return js.jsifyParenExpr(node)
	case *ast.SelectorExpr:
		return js.jsifySelectorExpr(node)
	case *ast.IndexExpr:
		return js.jsifyIndexExpr(node)
	case *ast.IndexListExpr:
		// for type parameters, skip
		return nil
	case *ast.SliceExpr:
		return js.jsifySliceExpr(node)
	case *ast.TypeAssertExpr:
		typAndVal := js.pkg.TypesInfo.Types[node.Type]
		if !typAndVal.HasOk() {
			return nil
		}

		typ := typAndVal.Type.(*types.Named)
		switch typ := typ.Underlying().(type) {
		case *types.Interface:
			if typ.NumMethods() == 0 {
				// simple case
				return nil
			}
		case *types.Struct:

		}
		return nil
	case *ast.CallExpr:
		// panic("not implemented")
		js.write("<call expr>")
		return nil
	case *ast.StarExpr:
		return js.jsifyStarExpr(node)
	case *ast.UnaryExpr:
		return js.jsifyUnaryExpr(node)
	case *ast.BinaryExpr:
		return js.jsifyBinaryExpr(node)
	case *ast.KeyValueExpr:
		return js.jsifyKeyValueExpr(node)
	}

	js.write("<unk>")
	return fmt.Errorf("unknown expr %T on %s", node, js.pkg.Fset.Position(node.Pos()))
}

func (js *jsifier) jsifyIdent(node *ast.Ident) error {
	js.buf.WriteString(node.Name)
	return nil
}

func (js *jsifier) jsifySliceExpr(node *ast.SliceExpr) error {
	js.write("go.slice(")

	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	js.write(", ")

	if node.Low != nil {
		if err := js.jsifyExpr(node.Low); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}
	} else {
		js.write("undefined")
	}

	js.write(", ")

	if node.High != nil {
		if err := js.jsifyExpr(node.High); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}
	} else {
		js.write("undefined")
	}

	js.write(", ")

	if node.Max != nil {
		if err := js.jsifyExpr(node.Max); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}
	} else {
		js.write("undefined")
	}

	js.write(")")
	return nil
}

func (js *jsifier) jsifyIndexExpr(node *ast.IndexExpr) error {
	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	js.write("[")

	if err := js.jsifyExpr(node.Index); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	js.write("]")
	return nil
}

func (js *jsifier) jsifySelectorExpr(node *ast.SelectorExpr) error {
	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	js.write(".")
	js.buf.WriteString(node.Sel.Name)
	return nil
}

func (js *jsifier) jsifyParenExpr(node *ast.ParenExpr) error {
	js.write("(")

	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	js.write(")")

	return nil
}

func (js *jsifier) jsifyKeyValueExpr(node *ast.KeyValueExpr) error {
	if err := js.jsifyExpr(node.Key); err != nil {
		return fmt.Errorf("jsify key expr: %w", err)
	}

	js.write(": ")

	if err := js.jsifyExpr(node.Value); err != nil {
		return fmt.Errorf("jsify value expr: %w", err)
	}

	return nil
}

func (js *jsifier) jsifyCompositeLit(node *ast.CompositeLit) error {
	typAndVal := js.pkg.TypesInfo.Types[node]
	_, isArray := typAndVal.Type.(*types.Array)
	if !isArray {
		_, isArray = typAndVal.Type.(*types.Slice)
	}

	if isArray {
		js.write("Array(")
	} else {
		js.write("Object.create({")
	}

	if len(node.Elts) != 0 {
		js.write("\n")
	}

	for _, elt := range node.Elts {
		if err := js.jsifyExpr(elt); err != nil {
			return fmt.Errorf("jsify expr: %w", err)
		}
		js.write(",\n")
	}

	if isArray {
		js.write(")")
	} else {
		js.write("})")
	}
	return nil
}

func (js *jsifier) jsifyFuncLit(node *ast.FuncLit) error {
	if err := js.jsifyFuncType(node.Type); err != nil {
		return fmt.Errorf("jsify func type: %w", err)
	}

	if err := js.jsifyBlockStmt(node.Body); err != nil {
		return fmt.Errorf("jsify block stmt: %w", err)
	}

	return nil
}

func (js *jsifier) jsifyStarExpr(node *ast.StarExpr) error {
	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	js.write(".unref()")
	return nil
}

func (js *jsifier) jsifyUnaryExpr(node *ast.UnaryExpr) error {
	switch node.Op {
	case token.ADD, token.SUB, token.NOT, token.XOR, token.MUL, token.AND:
	case token.ARROW:
		return errors.New("arrow operator not implemented")
	default:
		return fmt.Errorf("operator %s not supported", node.Op)
	}

	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}
	return nil
}

func (js *jsifier) jsifyBinaryExpr(node *ast.BinaryExpr) error {
	if err := js.jsifyExpr(node.X); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	js.write(" ")

	switch node.Op {
	case token.LOR, token.LAND,
		token.EQL, token.NEQ, token.LSS, token.LEQ, token.GTR, token.GEQ,
		token.ADD, token.SUB, token.OR, token.XOR,
		token.MUL, token.QUO, token.REM, token.SHL, token.SHR, token.AND:
		js.write(node.Op.String())
	default:
		return fmt.Errorf("operator %s not supported", node.Op)
	}

	js.write(" ")

	if err := js.jsifyExpr(node.Y); err != nil {
		return fmt.Errorf("jsify expr: %w", err)
	}

	return nil
}

func (js *jsifier) jsifyBasicLit(node *ast.BasicLit) error {
	typAndVal := js.pkg.TypesInfo.Types[node]
	typ, ok := typAndVal.Type.(*types.Basic)
	if !ok {
		return errors.New("expected *types.Basic for expr of *ast.BasicLit")
	}

	switch node.Kind {
	case token.INT:
		if isMaybeOctalLit(node.Value) {
			node.Value = normalizeOctalLit(node.Value)
		}

		node.Value = intLitToJs(node.Value)
	case token.FLOAT:
		if isHexLitWithMantissaP(node.Value) {
			return errors.New("p exponent not supported")
		}
	}

	js.write("go.")
	switch typ.Kind() {
	case types.Int, types.UntypedInt:
		js.write("int")
	case types.Int8:
		js.write("int8")
	case types.Int16:
		js.write("int16")
	case types.Int32:
		js.write("int32")
	case types.Int64:
		js.write("int64")
	case types.Uint:
		js.write("uint")
	case types.Uint8:
		js.write("uint8")
	case types.Uint16:
		js.write("uint16")
	case types.Uint32, types.UntypedRune:
		js.write("uint32")
	case types.Uint64:
		js.write("uint64")
	case types.Float32:
		js.write("float32")
	case types.Float64, types.UntypedFloat:
		js.write("float64")
	case types.Bool, types.UntypedBool:
		js.write("bool")
	case types.String, types.UntypedString:
		js.write("string")
	default:
		return fmt.Errorf("literal %s unsupported (type - %s)", node.Value, typ)
	}

	js.write("(" + node.Value + ")")

	return nil
}

func isMaybeOctalLit(s string) bool {
	if len(s) < 2 {
		return false
	}

	if s[0] != '0' {
		return false
	}

	if s[1] >= '0' && s[1] <= '7' {
		return true
	}

	if len(s) == 2 {
		return false
	}

	if !(s[1] == 'o' || s[1] == 'O') {
		if s[1] != '_' {
			return false
		}
	}

	if s[2] == '_' && len(s) == 3 {
		return false
	}

	return true
}

func normalizeOctalLit(v string) string {
	var sb strings.Builder
	sb.WriteByte(v[0])
	if !(v[1] == 'o' || v[1] == 'O') {
		sb.WriteByte('o')
	}

	sb.WriteString(v[1:])
	return sb.String()
}

func intLitToJs(v string) string {
	if len(v) < 3 {
		return v
	}

	var sb strings.Builder
	sb.WriteString(v[:2])
	if v[2] == '_' {
		sb.WriteString(v[3:])
	} else {
		sb.WriteString(v[2:])
	}

	return sb.String()
}

var isHexLitWithMantissaPRegexp = regexp.MustCompile(`^0(x|X)[0-9a-fA-F_\.]+(p|P).+`)

func isHexLitWithMantissaP(v string) bool {
	return isHexLitWithMantissaPRegexp.MatchString(v)
}
