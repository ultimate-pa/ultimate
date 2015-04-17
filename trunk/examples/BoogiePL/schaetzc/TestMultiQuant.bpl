//#Unsafe

// Preprocessor throws AssertionError, when inlining is enabled.
// Odd fact: It passes, if sub() is changed to have no return value.

procedure sub() returns (ret : bool) {
}

procedure main()
{
  var localVar : bool;
  call localVar := sub();
  assert (forall x : int :: x > 0);
  assert (forall x : int :: x != 0);
}

