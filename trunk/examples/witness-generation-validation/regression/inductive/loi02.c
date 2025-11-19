// #Safe
/*
 * TODO: We do not report an invariant for label_712 because it is merged into label_706.
 *
 * Date: 2025-11-12
 * Author: matthias.heizmann@iste.uni-stuttgart.de
 *
 */

int main() {
  int x = 1;
  label_706:;
  if (__VERIFIER_nondet_int()) {
    label_712:;
    goto label_706;
  } else {
    assert(x==1);
    goto label_712;
  }
}
