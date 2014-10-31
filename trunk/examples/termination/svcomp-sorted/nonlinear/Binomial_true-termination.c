// public class Binomial {
    
    // public static int fact(int n) {
	// if (n <= 0) return 1;
	// else return n * fact(n - 1);
    // }

    // public static int binomialCoefficient(int n, int k) {
	// return fact(n) / (fact(k) * fact(n - k));
    // }

    // public static void main(String args[]) {
	// for (int n = 0; n <= args.length; n++)
	    // for (int k = 0; k <= args.length; k++)
		// if (k <= n) binomialCoefficient(n, k);
		// else binomialCoefficient(k, n);
    // }
	
	
// }

extern int __VERIFIER_nondet_int(void);

int fact(int n) {
	if (n <= 0) return 1;
	else return n * fact(n - 1);
}
	
int binomialCoefficient(int n, int k) {
	return fact(n) / (fact(k) * fact(n - k));
}

int main() {
	int x = __VERIFIER_nondet_int();
	if(x < 0)
		return 0;
	int y = __VERIFIER_nondet_int();
	if(y < 0) 
		return 0;
	int z = __VERIFIER_nondet_int();
	for (int n = 0; n <= x; n++)
	    for (int k = 0; k <= x; k++)
		if (k <= n) binomialCoefficient(n, k);
		else binomialCoefficient(k, n);
    }
