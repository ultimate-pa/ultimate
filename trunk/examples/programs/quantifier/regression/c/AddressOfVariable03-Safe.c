//#Safe
// testing the functionality that a variable whose address is read in the
// program has to be stored on the heap by the translation
// (the translation result should be the same as for the statements in the 
// comments)
// note that this does intentionally not include the possibility of writing
// addresses to ints -- we consider that an implicit cast and (may) treat
// it elsewhere
//author: nutz

int main() {
	int v; 		// int* v;
	int* addrV;	// int* addrV;
	int* addr2;	// int* addr2;
	int w;		// int w;
	int x;

	addrV = &v; 	// addrV =  &*v;
	addr2 = addrV;	// addr2 = addrV;
	w = v;		// w = *v
	
	return 0;
}
