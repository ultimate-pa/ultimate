//#Safe
/*
* This Boogie code was automatically generated from weaver benchmarks <https://github.com/weaver-verifier/weaver>.
* The original file name was 'weaver/examples/popl20/figure1.wvr'.
*
* Generated: 2021-02-25T09:33:25.
*
* Info: ConComChecker proves the condition (not (= counter 0)), which results in an improvement from a timeout (>900s) to ~10s
*/
var i1 : int;
var i2 : int;
var N1 : int;
var N2 : int;
var counter : int;


procedure thread1() returns ()
modifies i1, i2, N1, N2, counter;
{
  while (( i1 < N1 )) {
    atomic {
      counter := ( counter + 1 );
      i1 := ( i1 + 1 );
    }
  }
}

procedure thread2() returns ()
modifies i1, i2, N1, N2, counter;
{
  while (( i2 < N2 )) {
    atomic {
      assume ( 0 < counter );
      counter := ( counter - 1 );
      i2 := ( i2 + 1 );
    }
  }
}

procedure ULTIMATE.start() returns ()
modifies i1, i2, N1, N2, counter;
{
  assume ( i1 == 0 );
  assume ( counter == 0 );
  assume ( i2 == 0 );
  assume ( N1 == N2 );
  fork 1 thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;
  assume !( counter == 0 );
  assert false; // should be unreachable
}
