//#Unsafe
/*
 * memory unsafe access, possibly not detected because of wrong overflow handling
 *
 * relevant settings;
 *  bitvector
 *  32bit
 *  memsafety
 *
 */
int main() {
  int * a = malloc(sizeof(int));

  // writing at 2^31 - 4, adding sizeof(int) gives a negative number, which 
  // our check recognizes as "in bounds"
  int i = 0x1fffffff;
  a[i] = 1;
  free(a);
}
