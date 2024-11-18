//#Safe
/*
* This Boogie code was automatically generated from weaver benchmarks <https://github.com/weaver-verifier/weaver>.
* The original file name was 'weaver/examples/test/context1.wvr'.
*
* Generated: 2021-02-25T09:33:24.
*
* Info: ConComChecker proves the condition (not (= size 0)), which results in an improvement from a timeout (>900s) to ~10s
*/
var queue : [int] int;
var front : int;
var size : int;
var x : int;


procedure thread1() returns ()
modifies queue, front, size, x;
{
  while (*) {
    atomic {
      assume ( queue[( front + size )] == 5 );
      size := ( size + 1 );
    }
  }
}

procedure thread2() returns ()
modifies queue, front, size, x;
{
  while (*) {
    atomic {
      assume ( size > 0 );
      x := queue[front];
      front := ( front + 1 );
      size := ( size - 1 );
    }
  }
}

procedure ULTIMATE.start() returns ()
modifies queue, front, size, x;
{
  assume ( ( size == 0 ) && ( x == 5 ) );
  fork 1 thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;
  assume !( x == 5 );
  assert false; // should be unreachable
}
