//#Unsafe
// Date: 2026-11-18
// An enumeration constant between INT_MAX and UINT_MAX (common in Linux drivers, e.g. FE_CAN_MUTE_TS = 0x80000000 in
// SV-COMP LDV tasks) has the enumerated type, which GCC makes unsigned int (C23 6.7.2.2). Its conversion to int is
// implementation-defined, GCC reduces it modulo 2^32, so x is negative.

extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "EnumUnsignedIntConstant-Unsafe.c", 8, "reach_error"); }

enum fe_caps { FE_IS_STUPID = 0, FE_CAN_INVERSION_AUTO = 0x1, FE_CAN_MUTE_TS = 0x80000000 };

int main() {
	int x = (int)FE_CAN_MUTE_TS;
	if (x < 0) {
		reach_error();
	}
	return 0;
}
