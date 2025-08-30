package heap

import "github.com/goose-lang/std"

func Swap(x *int, y *int) {
	old_y := *y
	*y = *x
	*x = old_y
}

// IgnoreOne has a specification that shows it does not need ownership of
// its second argument.
func IgnoreOne(x *int, y *int) {
	std.Assert(*x == 0)
	*x = 42
}

// UseIgnoreOneOwnership uses IgnoreOneLocF and can be verified using its
// specification.
func UseIgnoreOneOwnership() {
	x := 0
	y := 42
	IgnoreOne(&x, &y)
	std.Assert(x == y)
}

// CopySlice copies from src to dst
//
// dst must be at least as long as src
func CopySlice(dst []byte, src []byte) {
	l := uint64(len(dst))
	for i := uint64(0); i < l; i++ {
		dst[i] = src[i]
	}
}

// StackEscape shows a local variable being promoted to the heap.
//
// This illustrates both how Go works and ownership principles.
func StackEscape() *int {
	x := 42
	return &x
}
