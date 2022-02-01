//#Unsafe

// Preprocessor throws AssertionError (with or without inlining)

procedure sub() returns () {
}

procedure main()
{
  var localVar : bool;
  assert (forall x : int :: x > 0);
  assert (forall x : int :: x != 0);
  call sub();
}

