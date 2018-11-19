//#Unsafe
int main() {

  int * p;
  if (1) {
    p = & (int) { -1 };
  }

  int x;
  /* this is memory unsafe, since the compound literal that p pointed to went 
   * out of scope */
  x = *p;
}
