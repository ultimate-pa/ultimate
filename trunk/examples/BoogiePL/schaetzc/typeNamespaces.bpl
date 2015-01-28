// Local type names can shadow global type names, according to "This is Boogie 2".
// Microsoft's Boogie implementation and Boogalo don't allow shadowing of type names.

type T;
procedure f<T>(i : T) {
  //var m: <T> [T] int;
  //assert (forall<T> x : T :: x == x);
}

