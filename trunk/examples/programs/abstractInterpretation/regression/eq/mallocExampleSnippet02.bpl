//#Safe
/*
 * Writes a value into a two dimensional array and then retrieves it.
 */

var #memory_int : [int,int]int;

procedure foo() ;
modifies #memory_int;

implementation foo() {

  var res, p.base, p.offset, main_~v~1 : int;
  var ptr.base, ptr.offset : int;
  var read~int_#value : int;

  #memory_int[p.base, p.offset] := 6;

  ptr.base, ptr.offset := p.base, p.offset;
  havoc read~int_#value;
  assume read~int_#value == #memory_int[ptr.base,ptr.offset];
  main_~v~1 := read~int_#value;

  assert main_~v~1 == 6;

}

