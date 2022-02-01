/*
 * minimal test for the "onHeap" functionality where we store non-pointer
 * variables on the heap, because they are addressoffed somewhere in the 
 * program.
 * author: nutz, 18.12.2013
 */
int main() {
	int i, *ip;
	ip = &i;
}
