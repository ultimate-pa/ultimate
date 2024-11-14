//#Safe
/*
* This Boogie code was automatically generated from weaver benchmarks <https://github.com/weaver-verifier/weaver>.
* The original file name was 'weaver/examples/popl20/min-max-inc.wvr'.
*
* Generated: 2021-02-25T09:33:25.
*/
var A : [int] int;
var min : int;
var max : int;
var i : int;
var j : int;
var k : int;
var l : int;
var N : int;
var v_assert : bool;
var b1 : bool;
var b2 : bool;


procedure thread1() returns ()
modifies A, min, max, i, j, k, l, N, v_assert, b1, b2;
{
  min := A[ 0 ];
  b1 := true;
  while (( i < N )) {
    atomic {
      min := ( if ( min < A[ i ] ) then min else A[ i ] );
      i := ( i + 1 );
    }
  }
}

procedure thread2() returns ()
modifies A, min, max, i, j, k, l, N, v_assert, b1, b2;
{
  max := A[ 0 ];
  b2 := true;
  while (( j < N )) {
    atomic {
      max := ( if ( max > A[ j ] ) then max else A[ j ] );
      j := ( j + 1 );
    }
  }
}

procedure thread3() returns ()
modifies A, min, max, i, j, k, l, N, v_assert, b1, b2;
{
  while (( k < N )) {
    atomic {
      A[ k ] := ( A[ k ] + 1 );
      k := ( k + 1 );
    }
  }
}

procedure thread4() returns ()
modifies A, min, max, i, j, k, l, N, v_assert, b1, b2;
{
  v_assert := ( b1 ==> b2 ==> ( min <= ( max + 1 ) ) );
}

procedure ULTIMATE.start() returns ()
modifies A, min, max, i, j, k, l, N, v_assert, b1, b2;
{
  assume ( ( i == j && i == k && i == l && i == 0 ) && ( v_assert == b1 && v_assert == b2 && v_assert == false ) );
  fork 1 thread1();
  fork 2,2 thread2();
  fork 3,3,3 thread3();
  fork 4,4,4,4 thread4();
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;
  assume !v_assert;
  assert false; // should be unreachable
}
