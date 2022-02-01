//#Safe
/*
 * This example is made for settings with large block encoding 
 * (SequenceOfStatements or LoopFreeBlock).
 * It is supposed to check what happens if we access an array at an auxVar. In
 * a Transformula.
 *
 */
int main() {
  int i = 0;
  int j = 1;
  int a[10];
  // this value of j should neither be associated with an in nor with an outvar in LBE ssa
  j = i;
  a[j];
  j = 1;

}
