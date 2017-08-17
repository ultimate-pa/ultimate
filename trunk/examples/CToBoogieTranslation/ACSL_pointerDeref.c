//#Safe
/*
 * This example checks if we can deal with pointer dereferences in ACSL 
 * annotations.
 *
 * author: Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
int main() {
	int *p = malloc(sizeof(int));
	*p = 123;
	//@assert *p == 123;
}
