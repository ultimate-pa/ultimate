// testing the functionality that a variable whose address is read in the
// program has to be stored on the heap by the translation
// (the translation result should be the same as for the statements in the 
// comments)

int main() {
	int v; 		// int* v;
	int* addrV;	// int* addrV;
	int* addr2;	// int* addr2;
	int w;		// int* w;
	int x;

	addrV = &v; 	// *addrV =  &*v;   --> write ptr -> addrV 
	addr2 = addrV;	// *addr2 = *addrV;  --> write int -> addrV
	w = v;		// *w = *v
	x = 5;
	
	return 0;
}
