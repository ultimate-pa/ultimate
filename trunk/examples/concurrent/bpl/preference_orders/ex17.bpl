//#Safe
/*
* This Boogie code was automatically generated from weaver benchmarks <https://github.com/weaver-verifier/weaver>.
* The original file name was 'weaver/examples/parallel/parallel-sum-1.wvr'.
*
* Generated: 2021-02-25T09:33:22.
*
* Idea: thread1 and thread2 together compute the sum of some elements in an array;
*       thread3 and thread4 together compute the same sum; so the results should be equal.
*
* The optimal schedules would have the form ((t1 + t2) (t3 + t4))*,
*     as this allows for the simple invariant s1 == s2.
*
* May be possible with sequential (similar to ex16): (t1 t3)* (t2 t3)* (t1 t4)* (t2 t)*; perhaps using if-else to distinguish which thread exits one of the sub-expressions
*/
var x : [int] int;
var i1 : int;
var i2 : int;
var t11 : int;
var t21 : int;
var t12 : int;
var t22 : int;
var s1 : int;
var s2 : int;
var n : int;


procedure thread1() returns ()
modifies x, i1, i2, t11, t21, t12, t22, s1, s2, n;
{
  while (*) {
    atomic {
      assume ( i1 < n );
      i1 := ( i1 + 1 );
      t11 := x[i1];
    }
    s1 := ( s1 + t11 );
  }
}

procedure thread2() returns ()
modifies x, i1, i2, t11, t21, t12, t22, s1, s2, n;
{
  while (*) {
    atomic {
      assume ( i1 < n );
      i1 := ( i1 + 1 );
      t21 := x[i1];
    }
    s1 := ( s1 + t21 );
  }
}

procedure thread3() returns ()
modifies x, i1, i2, t11, t21, t12, t22, s1, s2, n;
{
  while (*) {
    atomic {
      assume ( i2 < n );
      i2 := ( i2 + 1 );
      t12 := x[i2];
    }
    s2 := ( s2 + t12 );
  }
}

procedure thread4() returns ()
modifies x, i1, i2, t11, t21, t12, t22, s1, s2, n;
{
  while (*) {
    atomic {
      assume ( i2 < n );
      i2 := ( i2 + 1 );
      t22 := x[i2];
    }
    s2 := ( s2 + t22 );
  }
}

procedure ULTIMATE.start() returns ()
modifies x, i1, i2, t11, t21, t12, t22, s1, s2, n;
{
  assume ( s1 == s2 && s1 == i1 && s1 == i2 && s1 == 0 );
  fork 1 thread1();
  fork 2,2 thread2();
  fork 3,3,3 thread3();
  fork 4,4,4,4 thread4();
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;
  assume ( ( i1 == i2 && i1 == n ) && !( s1 == s2 ) );
  assert false; // should be unreachable
}
