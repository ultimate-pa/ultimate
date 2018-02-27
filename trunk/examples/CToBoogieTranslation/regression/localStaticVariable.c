/*
 * test for static variables -- sv should be 
 * initialized and stored globally in Boogie
 * but should also have its own namespace (i.e. not
 * written/read in main()
 * author: nutz, 18.12.2013
 */
int f(int x) {
	static int sv = 5;
	sv++;
	return x + sv;
}

int main() {
	int sv = 0;
	sv = sv + f(sv);
	sv = f(sv);
}
