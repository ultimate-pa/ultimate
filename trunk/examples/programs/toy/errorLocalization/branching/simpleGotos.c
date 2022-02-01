//#Unsafe
//author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
//Simple goto example

void main() {
	int a;
	int x;
	a = 4;
	if(a == 4){
		x = 1;
		a = 3;
		if(x != 1){
			goto pos1;
		}
		x++;
	}
	x = 3;
	pos1:
		x=2;
	if(a == 3) __VERIFIER_error();
}
