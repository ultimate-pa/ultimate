//#termcomp16-someonesaidyes
extern int __VERIFIER_nondet_int();
int rec1(int i);
int rec2(int j);

int rec1(int i) {
	if(i <= 0)
		return 0;
	return rec2(rec1(i+1));
}

int rec2(int j) {
	if(j <= 0)
		return 0;
	return rec1(rec2(j-1));
}

int main() {
	int x = __VERIFIER_nondet_int();
	rec2(x);
}