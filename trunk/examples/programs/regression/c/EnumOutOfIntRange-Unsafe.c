//#Unsafe
// Date: 2026-11-17
// Enumeration constants whose value is not representable as int are a GNU extension (standardized only in C23);
// GCC then chooses a 64-bit unsigned integer type as the underlying type of the enumeration. Ultimate translates every
// enumeration type to int and wrongly proved this program correct (the cast to int was not reduced). Ultimate now
// refuses such enumerations. The expected result is UNKNOWN (unsupported syntax), never SAFE.
// Origin: sv-benchmarks c/firmware-common-simple/enum_int_cast.bug.c (SV-COMP 2027, Apache-2.0)

extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "EnumOutOfIntRange-Unsafe.c", 9, "reach_error"); }

typedef enum { VALUE = 0x8000000000000000 } enum_t;

enum_t foo() { return VALUE; }

int main() {
	// GCC reduces a value that cannot be represented in int modulo 2^32, so x becomes 0
	int x = (int)foo();
	enum_t y = (enum_t)x;
	if (!(y == 0x8000000000000000)) {
		reach_error();
		return 1;
	}
	return 0;
}
