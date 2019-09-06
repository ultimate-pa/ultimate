// #Safe
// Example from issue #444.
// https://github.com/ultimate-pa/ultimate/issues/444
//

function b(int) returns (int);
axiom b(0) == 0;

procedure f() {
  assert true;
}