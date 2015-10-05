extern int __VERIFIER_nondet_int();


int rec(int a) {
	if(a == 0)
		return 0;
	else {
		int res = rec(a-1);
		int rescopy = res;
		while(rescopy > 0)
			rescopy--;
		return 1 + res;
	}
}

int main() {
	int i = __VERIFIER_nondet_int();
	if(i <= 0)
		return 0;
	int res = rec(i);
	
}
