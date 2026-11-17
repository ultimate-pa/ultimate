//#Safe
// Date: 2026-11-17
// A pointer that is converted to an integer and back is the same pointer. Our pointer-integer conversions are not
// inverse to each other, so Ultimate reported a spurious violation. The conversion of a bitwise operation on a
// pointer-to-integer cast back to a pointer is now an overapproximation, hence the expected result is SAFE or UNKNOWN,
// never UNSAFE.
// Simplified from sv-benchmarks c/aws-c-common/aws_byte_cursor_advance_nospec_harness.i (SV-COMP 2027)

extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "IntegerToPointerRoundTrip-Safe.c", 9, "reach_error"); }
extern int __VERIFIER_nondet_int(void);

typedef unsigned long uintptr_t;

int main() {
	char buf[4];
	char *p = buf;
	uintptr_t mask = __VERIFIER_nondet_int() ? ~(uintptr_t)0 : (uintptr_t)-1;
	char *q = (char *)((uintptr_t)p & mask);
	if (q != p) {
		reach_error();
	}
	return 0;
}
