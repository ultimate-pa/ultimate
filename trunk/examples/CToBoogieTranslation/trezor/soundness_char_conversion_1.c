int main(void) {
  int data[256];
  char c = '\xff';
  int ic = (int)c;
  /* if the type 'char' defaults to signed char for the compiler used,
     ic will have the value of -1 and this is an out of bounds array access
     Otherwise, ic is 255 and this access is valid. */
  return data[ic];
}
