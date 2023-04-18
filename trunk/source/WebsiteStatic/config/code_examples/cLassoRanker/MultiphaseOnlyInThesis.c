// #rTermination
// Linear loop program that has the 3-phase ranking function
//     f3 = z + 1, f2 = y + 1, and f1 = x + 1
// according to the definition in Jan's master thesis,
//     https://users.cecs.anu.edu.au/~leike/Ranking%20Function%20Synthesis%20for%20Linear%20Lasso%20Programs%20-%20Leike%202013.pdf
// but does not have a multiphase ranking function according to the definition 
// in used in our TACAS paper.
//     2014TACAS - Leike,Heizmann - Ranking Templates for Linear Loops
// The above mentioned function is not a multiphase ranking function according
// to the paper because f2<0 does not imply that f3 is decreasing.
//
// We thank Amir Ben-Amram for pointing out that both definitions are not 
// equivalent.
//
//
// Author: Jan Leike, Matthias Heizmann
// Date: 2015-02-9

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	while (z >= 0) {
		if (x < 0 && y < 0) {
			z = z - 1;
		}
		y = y - x;
		x = x - 1;
	}
}
