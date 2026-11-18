//#Safe
// Date: 2026-11-18
// The integer type of an enumerated type follows GCC if a value is not representable as int (C23 6.7.2.2): unsigned
// int if no value is negative and all fit, otherwise a 64-bit type, unsigned if no value is negative. Enumeration
// constants representable as int have type int, all others have the enumerated type.

extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "EnumUnderlyingType-Safe.c", 8, "reach_error"); }

enum small { S_NEG = -1, S_ZERO, S_ONE };
enum fe_caps { FE_CAN_INVERSION_AUTO = 0x1, FE_CAN_MUTE_TS = 0x80000000 };
enum mask { DBG_ANY = 0xffffffff };
enum implicit { HIGH = 0xfffffffe, LAST };
enum mixed { M_NEG = -1, M_BIG = 0x80000000 };
enum wide { W_TOP = 0xffffffff, W_NEXT };

struct holder {
	char c;
	enum mixed m;
	enum fe_caps caps;
};

int main() {
	if (sizeof(enum small) != 4 || sizeof(enum fe_caps) != 4 || sizeof(enum mixed) != 8 || sizeof(enum wide) != 8) {
		reach_error();
	}
	if (sizeof(FE_CAN_INVERSION_AUTO) != 4 || sizeof(FE_CAN_MUTE_TS) != 4 || sizeof(M_BIG) != 8
			|| sizeof(W_NEXT) != 8) {
		reach_error();
	}
	if (S_NEG >= 0 || S_ONE != 1) {
		reach_error();
	}
	// FE_CAN_MUTE_TS has type unsigned int, so it is positive and -1 is converted to unsigned int
	if (FE_CAN_MUTE_TS < 0 || FE_CAN_MUTE_TS != 2147483648U || DBG_ANY != (unsigned int)-1 || LAST != 0xffffffffU) {
		reach_error();
	}
	if (M_NEG >= 0 || M_BIG != 2147483648LL || W_NEXT != 4294967296ULL) {
		reach_error();
	}
	enum mixed m = M_NEG;
	if (m >= 0) {
		reach_error();
	}
	m = M_BIG;
	if (m <= 0) {
		reach_error();
	}
	// enumerated types on the heap
	struct holder h;
	struct holder *p = &h;
	p->m = M_BIG;
	p->caps = FE_CAN_MUTE_TS;
	if (h.m != 2147483648LL || h.caps != 2147483648U) {
		reach_error();
	}
	enum wide w = W_NEXT;
	enum wide *pw = &w;
	if (*pw != 4294967296ULL) {
		reach_error();
	}
	return 0;
}
