// #Safe
/*
 * TODO: We do not report an invariant for label_002 because it is only the target of a goto in a line before. Line number for label_001 is wrong (same line number as main).
 *
 * Date: 2025-11-12
 * Author: matthias.heizmann@iste.uni-stuttgart.de
 *
 */
int main(){
  int x = 1;
  label_001:;
  goto label_002;
  label_002:;
  assert(x == 1);
  goto label_001;
}
