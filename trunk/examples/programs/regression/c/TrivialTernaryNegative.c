//#Safe
/*
 * Slight variation for program in bug reported by Philipp Berger on github.
 * <https://github.com/ultimate-pa/ultimate/issues/510>
 *
 * Ternary condition with "true" condition was simplified incorrectly,
 * statements needed to compute branch result were lost.
 *
 * Bug introduced in commit 0f246ad.
 * <https://github.com/ultimate-pa/ultimate/commit/0f246ad8627f2e238c0f050e863074fa47aece7d>
 */
extern void __VERIFIER_error();
char var1 = 0;
char var2 = 0;
void step(void) {
	if (var2) {
		var1 = (1);
	}
}

int property() {
	return (0) ? (0) : ((var2) ? (var1 == (1)) : (1));
}
int main(void) {
	while (1) {
		step();
		if (!property()) {
			__VERIFIER_error();
		}
	}
	return 0;
}
