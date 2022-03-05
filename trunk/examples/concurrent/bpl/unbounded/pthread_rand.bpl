//#Safe

/*
 * Extracted from: svcomp/pthread-ext/07_rand.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-02-11
 *
 */

var state, m, seed: int;

procedure thread() returns()
modifies state, m, seed;
{
  var myrand, nexts : int;	

  atomic { assume m == 0; m := 1; }
  if (state == 0) {
    seed := 1;
    state := 1;
    atomic { assume m == 1; m := 0; }
    while (true) {
        assert seed != 0;
    }
  } else {
    assume nexts != seed && nexts != 0;
    //assert nexts != seed;
    seed := nexts;
    atomic { assume m == 1; m := 0; }
    myrand := nexts % 10;
    assert myrand <= 10;
  }
}

procedure ULTIMATE.start() returns()
modifies state, m, seed;
{
  state := 0;
  m := 0;

  while (true) {
    fork 0 thread();
  }
}