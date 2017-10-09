//#Safe
/*
 * (result checked via Automizer web interface on 07.10.2017)
 *
 * Reduced version of framing-example for TACAS paper. 
 * VPDomain should be able to prove this but is not, as of 07.10.2017.
 *
 * author: nutz@informatik.uni-freiburg.de
 */
 * author: nutz@informatik.uni-freiburg.de
 */
var valid, content : [int] int;

procedure ULTIMATE.start();
modifies valid, content;
implementation ULTIMATE.start() {
  var p, i : int;
  assume valid[p] == 1;
  call initList();
  assert valid[p] == 1;
}

procedure initList();
modifies valid, content;
implementation initList() {
  var i, j : int;

  havoc i;
  assume valid[i] == 0;
  valid[i] := 2;

  havoc i;
  assume valid[i] == 0;
  valid[i] := 2;

  havoc i;
  assume valid[i] == 0;
  valid[i] := 2;
}
