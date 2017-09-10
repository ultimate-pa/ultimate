//#Safe
var #valid : [int] int;

var #memory_int : [int] int;

procedure bla ();
modifies #valid, #memory_int;

implementation bla () {
   var p,q : int;
   var i,j : int;
   var m1,m2 : int;

   assume #valid[m1] == 0;
   p := m1;
   #valid[m1] := 1;

   assume #valid[m2] == 0;
   q := m2;
   #valid[m2] := 1;

   assert p != q;

   #memory_int[p] := i;
   #memory_int[q] := j;

   assert #memory_int[p] == i;
}
