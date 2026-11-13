// #Unsafe
/*
 * Counterpart of memcpy-PointerOnHeap-Safe.c: memcpy copies the values (and
 * only the given number of bytes), so this error is reachable.
 *
 * Date: 2026-11-11
 * Author: max.barth95@gmx.de
 */
#include <string.h>

int main() {
	unsigned char src[16];
	unsigned char dst[16];
	unsigned char *p = src;
	// p has its address taken, so pointers are stored on the heap
	unsigned char **pp = &p;

	src[0] = 17;
	src[8] = 42;
	dst[8] = 5;
	memcpy(dst, src, 8);
	if (dst[0] == 17 && dst[8] == 5) {
		reach_error();
	}
	return 0;
}
