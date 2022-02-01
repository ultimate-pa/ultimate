// public class LeUserDefRec {
	// public static void main(String[] args) {
		// int x = args[0].length();
		// int y = args[1].length();
		// le(x, y);
	// }

	// public static boolean le(int x, int y) {
		// if (x > 0 && y > 0) {
			// return le(x-1, y-1);
		// } else {
			// return (x == 0);
		// }
	// }
// }

extern int __VERIFIER_nondet_int(void);
int le(int x, int y);
int random(void);

int main() {
	int x = __VERIFIER_nondet_int();
	if(x < 0)
		return 0;
	int y = __VERIFIER_nondet_int();
	if(y < 0) 
		return 0;
	int z = __VERIFIER_nondet_int();
	le(x,y);

}

int random() {
	int x = __VERIFIER_nondet_int();
	if (x < 0)
		return -x;
	else
		return x;
}

int le(int x, int y) {
		if (x > 0 && y > 0) {
			return le(x-1, y-1);
		} else {
			return (x == 0);
		}
}
