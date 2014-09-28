// #Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-09-28
 *
 */

procedure method1(a : int, b : int) returns (res : int){
  res := b - a;
}

procedure method2(c : int, d : int) returns (#res : int){
    var tmp : int;
    call tmp := method1(c, d);
    #res := c + tmp;
}

procedure main() returns (main : int){
    var k : int;

    call k := method2(10, 11);
    assert k == 11;
}
