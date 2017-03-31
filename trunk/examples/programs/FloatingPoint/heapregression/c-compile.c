//#Safe
//
// Author: greitsch@informatik.uni-freiburg.de
//
// Date  : 2017-03-31
//
// Auxiliary file that allows to run make in the directory to compile each
// regression test.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

char *callFilename;

extern void __VERIFIER_error() {
	if (strstr(callFilename, "unsafe") == NULL) {
		printf("ERROR\n");
		exit(1);
	}
}

extern int nonMain();

int main(int argc, char* argv[])
{
	callFilename = argv[0];
	//@ assert \true;
	return nonMain();
}
