// #Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-09-28
 *
 */

procedure inner(a : int, b : int) returns (res : int){
  res := b - a;
}

procedure outer(c : int, d : int) returns (#res : int){
    var tmp : int;
    call tmp := inner(c, d);
    #res := c + tmp;
}

procedure main() returns (main : int){
    var k : int;

    call k := outer(10, 11);
    assert k == 11;
}
