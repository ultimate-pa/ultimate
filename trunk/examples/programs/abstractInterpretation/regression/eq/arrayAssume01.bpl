//#Safe

procedure foo() {
  var #valid1 : [int] int;
  var #valid2 : [int] int;
  assume #valid1 == #valid2[0 := 0];
  assert #valid1[0] == 0;
}
