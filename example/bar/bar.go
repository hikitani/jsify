package bar

func Bar() {
	a := 1
	_ = a
	{
		a := 2
		_ = a
	}
}
