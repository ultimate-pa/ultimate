// #Unsafe
/*
 * Extracted from goblint-regression/13-privatized_19-publish-precision_unknown_1_pos.i
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-11-24
 */

var glob, mutex : int;

procedure thread()
modifies glob, mutex;
{
  atomic { assume mutex == 0; mutex := 1; }
  glob := 5;
  mutex := 0;
  atomic { assume mutex == 0; mutex := 1; } // Critical statement
}
procedure ULTIMATE.start()
modifies glob, mutex;
{
  glob := 0;
  mutex := 0;
  fork 0 thread();
  atomic { assume mutex == 0; mutex := 1; } // Critical statement
  assert glob == 0;
  mutex := 0;
}