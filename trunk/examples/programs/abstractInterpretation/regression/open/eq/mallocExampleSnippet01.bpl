//#Safe

var #valid : [int]int;


procedure foo() ;
modifies #valid;

implementation foo() {
  var #Ultimate.alloc_old_#valid : [int]int;

  var res, p, q : int;

  #Ultimate.alloc_old_#valid := #valid;
  havoc #valid;
  assume #Ultimate.alloc_old_#valid[res] == 0;
  assume #valid == #Ultimate.alloc_old_#valid[res := 1];
  p := res;

  #Ultimate.alloc_old_#valid := #valid;
  havoc #valid;
  assume #Ultimate.alloc_old_#valid[res] == 0;
  assume #valid == #Ultimate.alloc_old_#valid[res := 1];
  q := res;

  assert p != q;
}
