//#Unsafe (but safe if we do not check pointer validity at dereference
//
// Simplified version of example that I received from Jürgen
// The program is correctly verified
// - if we allocate memory for *curr (see (1)) or
// - if we comment the 'curr = *(char **)curr' line
//
// Author: Matthias Heizmann
// Date: 2015-03-05

void main() {
	char *prev;
	char *curr; // (1) = malloc(1*sizeof(char));
	if (*curr == 73) {
		prev = curr;
		curr = *(char **)curr;
		int prop1 = (*prev == 73);
		//@ assert (prop1 != 0);
	}
}

