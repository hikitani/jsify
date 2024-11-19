package foo

//go:jsify
func PrintHello() {
	// fmt.Println("Hello world!")
	// bar.Bar()
	a, b := 1, 2
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
}
