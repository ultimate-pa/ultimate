// #Safe
/*
 * memcpy has to copy the value of an int when the program also stores floats
 * on the heap (https://github.com/ultimate-pa/ultimate/issues/744). The
 * translation used to copy #memory_int and #memory_real through write
 * procedures, and each write procedure havocked the other heap array at the
 * address it wrote, so *i2 was arbitrary after memcpy.
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
	if (*i2 != 42) {
		reach_error();
	}

	// introduces #memory_real
	float* f1 = (float*) malloc(sizeof(float));
	*f1 = 44.0;

	return 0;
}
