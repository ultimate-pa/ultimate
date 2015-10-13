// public class TerminatorRec02 {
	// public static void main(String[] args) {
		// fact(args.length);
	// }

	// public static int fact(int x) {
		// if (x > 1) {
			// int y = fact(x - 1);
			// return y * x;
		// }
		// return 1;
	// }
// }

extern int __VERIFIER_nondet_int(void);

int fact(int x) {
		if (x > 1) {
			int y = fact(x - 1);
			return y * x;
		}
		return 1;
	}

int main() {
	int x = __VERIFIER_nondet_int();
	if(x < 0)
		return 0;
	int y = __VERIFIER_nondet_int();
	if(y < 0) 
		return 0;
	int z = __VERIFIER_nondet_int();
	fact(x);

}
