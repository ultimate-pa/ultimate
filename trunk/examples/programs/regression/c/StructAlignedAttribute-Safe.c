//#Safe
// Date: 2026-11-17
// Our computation of sizes and offsets ignores aligned attributes (and adds no padding), so Ultimate reported a
// spurious violation here. The size of a type with an aligned attribute is now an overapproximation, hence the
// expected result is SAFE or UNKNOWN, never UNSAFE.
// Origin: sv-benchmarks c/firmware-common-simple/packed_aligned.c (SV-COMP 2027, Apache-2.0)

extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "StructAlignedAttribute-Safe.c", 10, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

typedef struct {
	char c;
	int i;
} __attribute__((packed)) packed_t;

typedef struct {
	char c;
	int i;
} __attribute__((aligned(8))) aligned_t;

typedef struct {
	char c;
	packed_t i __attribute__((aligned(8)));
} packed_aligned_t;

int main() {
	__VERIFIER_assert(sizeof(packed_t) == 5);
	__VERIFIER_assert(sizeof(aligned_t) == 8);
	__VERIFIER_assert(sizeof(packed_aligned_t) == 16);
	return 0;
}
