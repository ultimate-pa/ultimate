// public class Parts {

    // public static int parts(int p, int q) {
	// if (p <= 0) return 1;
	// else if (q <= 0) return 0;
	// else if (q > p) return parts(p, p);
	// else return parts(p-q, q) + parts(p, q-1);
    // }

    // public static void main(String args[]) {
	// for (int p = 0; p <= args.length; p++)
	    // for (int q = 0; q <= args.length; q++)
		// parts(p, q);
    // }
// }

extern int __VERIFIER_nondet_int(void);

int parts(int p, int q) {
	if (p <= 0) return 1;
	else if (q <= 0) return 0;
	else if (q > p) return parts(p, p);
	else return parts(p-q, q) + parts(p, q-1);
    }

int main() {
	int x = __VERIFIER_nondet_int();
	if(x < 0)
		return 0;
	int y = __VERIFIER_nondet_int();
	if(y < 0) 
		return 0;
	int z = __VERIFIER_nondet_int();
	for (int p = 0; p <= x; p++)
	    for (int q = 0; q <= x; q++)
		parts(p, q);

}