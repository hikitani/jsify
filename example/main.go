package foo

type Foo struct {
	A int
	B string
}

//go:jsify
func PrintHello() {
	// fmt.Println("Hello world!")
	// bar.Bar()
	_ = any(1).(Foo)
	_, ok := any(1).(Foo)
	_ = ok

	a, b := 1, (2 + 1)
	_, _ = a, b
	_ = "asdasd"
	_ = 1.2123123
	_ = 0_123123
	_ = 0o_0

	const A = "Hello"

	var (
		B, C = 1, 2
		D    = "DDD"
	)
	_, _, _ = B, C, D

	if true {
		a = b
	}

	p := new(int)
	*p = 1
	*p += 1
	*p, a = 1, 2

	foo := Foo{
		A: 1,
		B: "2",
	}

	a = foo.A

	s := []int{1, 2, 3, 4, 5}
	_ = s
	_ = s[:]
	_ = s[:2]
	_ = s[1:]
	_ = s[1:2]
	_ = s[1:2:3]
}
