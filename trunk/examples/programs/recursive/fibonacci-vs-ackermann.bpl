//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 10.5.2011
 *
 * Correct iff the result of the ackermann function is bigger than the result
 * of fibonacci.
 * I guess, without a predicate like fibonacci(a)>b in the invariant of
 * ackermann we are not able to proof correctness.
 */

function fib(n: int) returns (res: int);
axiom (forall n: int :: n >= 2 ==> fib(n) == fib(n-1) + fib(n-2));
axiom fib(0) == 0;
axiom fib(1) == 1;

procedure Main(a: int);
free requires a >= 0;

implementation Main(a: int)
{
  var b, c: int;
  call b := ackermann(a,a);
  call c := fibonacci(a);
  assert ( b >= c);
}



procedure fibonacci(n: int) returns (res: int);
free requires n >= 0;
ensures res == fib(n);

implementation fibonacci(n: int) returns (res: int)
{
  var tmpFst, tmpSnd: int;

  if (n < 1) {
    res := 0;
  }
  else {
    if (n == 1) {
      res := 1;
    }
    else {
      call tmpFst := fibonacci(n-1);
      call tmpSnd := fibonacci(n-2);
      res := tmpFst + tmpSnd;
    }
  }
}



procedure ackermann(m,n: int) returns (res: int);

implementation ackermann(m,n : int) returns (res: int)
{
  var tmp: int;

  if (m==0) {
    res := n+1;
    return;
  }
  if (n==0) {
    call res := ackermann(m-1,1);
    return;
  }
  call tmp := ackermann(m,n-1);
  call res := ackermann(m-1,tmp);
}


