//#Unsafe

// Minimal example to reproduce the bug
// AssertionError: No corresponding IProgramVar for …
//
// This example was generated from svcomp/float-benchs/float_double.c
// It is important that the function application is used inside a
// ternary operator which is used inside a call statement.
// Using only the function, or function inside a ternary operator,
// or function (without ternary operator) inside a call statement
// does not trigger the bug.
// The annotation { :overapproximation "…" } is also important.


procedure ULTIMATE.start() {
    call p((if f() then 1 else 0));
}

procedure p(i: int) {
	assert false;
}

function { :overapproximation "f" } f() returns (out : bool);
