// public class Avg {
	// public static void main(String[] args) {
		// int x, y;
		// x = args[0].length();
		// y = args[1].length();
		// average(x,y);
	// }

	// public static int average(int x, int y) {
		// if (x > 0) {
			// return average(x-1, y+1);
		// } else if (y > 2) {
			// return 1 + average(x+1, y-2);
		// } else {
			// return 1;
		// }
	// }
// }

extern int __VERIFIER_nondet_int(void);
int average(int x,int y);
int random(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	average(random(),random());

}

int random() {
	int x = __VERIFIER_nondet_int();
	if (x < 0)
		return -x;
	else
		return x;
}



int average(int x, int y) {
		if (x > 0) {
			return average(x-1, y+1);
		} else if (y > 2) {
			return 1 + average(x+1, y-2);
		} else {
			return 1;
		}
	}
