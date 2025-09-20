// #Unsafe
/* Reveals soundness bug (that was detected thanks to our inductive witnesses).
 * We model a continue statement by a goto that jumps to an auxiliary label.
 * This label was placed at the beginning of the loop, whereas it should be placed directly before the loop to make sure that we check the loop invariant after each continue.
 * This bug affects not only soundness while checking loop invariants but also causes us to produce wrong loop invariants if there are continue statements.
 *
 *
 * Date: 2025-05-08
 * Author: matthias.heizmann@iste.uni-stuttgart.de
 *
 */

int main(void) {
  int i = 0;
  //@ loop invariant i == 0;
  while (i <= 1337) {
    i++;
    continue;
  }
  return 0;
}
