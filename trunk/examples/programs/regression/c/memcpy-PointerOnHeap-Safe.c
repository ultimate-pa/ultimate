// #Safe
/*
 * memcpy has to copy every byte, also at pointer-aligned offsets, when the
 * program stores pointers on the heap. The translation used to copy the data
 * arrays in one loop and the pointer array in a second loop whose write
 * procedure havocked the data arrays at dest, dest+8, ..., so dst[0] was
 * arbitrary afterwards.
 *
 * Date: 2026-11-11
 * Author: max.barth95@gmx.de
 */
#include <string.h>

int main() {
	unsigned char src[2];
	unsigned char dst[2];
	unsigned char *p = src;
	// p has its address taken, so pointers are stored on the heap
	unsigned char **pp = &p;

	src[0] = 17;
	memcpy(dst, src, 1);
	if (dst[0] != 17) {
		reach_error();
	}

	return 0;
}
