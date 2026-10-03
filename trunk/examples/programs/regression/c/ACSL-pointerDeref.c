//#Safe
/*
 * This example checks if we can deal with pointer dereferences in ACSL 
 * annotations.
 *
 * author: Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
int main() {
	int *p = malloc(sizeof(int));
	if (p == NULL) return;
	*p = 123;
	//@assert *p == 123;
}
