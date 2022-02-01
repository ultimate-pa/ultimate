//#Safe

procedure foo() {
  var #valid : [int] int;
  #valid := #valid[0 := 0];
  assert #valid[0] == 0;
}
