//#Unsafe
/*
 * At first look none of the statements look responsible. But havoc x is because
 * it can make the rest of the error trace blocking.
 *
 * Author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
 * Date: 2017-07-02
 */

procedure main() returns () {
    var x,a,b: int;
    havoc x;
    if(x > 10){
      x := x+1;
    }
    else {
      x := x-1;
    }
    assert a > b;
}
