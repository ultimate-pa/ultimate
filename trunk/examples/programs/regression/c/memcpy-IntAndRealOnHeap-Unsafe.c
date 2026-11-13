// #Unsafe
/*
 * Counterpart of memcpy-IntAndRealOnHeap-Safe.c: memcpy copies the value, so
 * this error is reachable.
 *
 * Date: 2026-11-12
 * Author: max.barth95@gmx.de
 */
#include <stdlib.h>
#include <string.h>

int main() {
	int* i = (int*) malloc(sizeof(int));
	*i = 42;

	int* i2 = (int*) malloc(sizeof(int));
	memcpy(i2, i, sizeof(int));
	if (*i2 == 42) {
		reach_error();
	}

	// introduces #memory_real
	float* f1 = (float*) malloc(sizeof(float));
	*f1 = 44.0;

	return 0;
}
