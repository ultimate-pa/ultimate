//#Safe

/*
 * Extracted from: svcomp/pthread-ext/33_double_lock_p1_vs.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-02-11
 *
 */

var mutexa, mutexb, count: int;

procedure thread1() returns()
modifies mutexa, mutexb;
{
  while (true) {
    atomic { assume mutexa == 0; mutexa := 1; }
	assert count >= -1;
	atomic { assume mutexb == 0; mutexb := 1; }
	assert count == 0;
	atomic { assume mutexb == 1; mutexb := 0; }
	atomic { assume mutexa == 1; mutexa := 0; }
  }
}

procedure thread2() returns()
modifies mutexa, mutexb, count;
{
  if (*) {
    atomic { assume mutexa == 0; mutexa := 1; }
	count := count + 1;
	count := count - 1;
	atomic { assume mutexa == 1; mutexa := 0; }
  } else {
    atomic { assume mutexb == 0; mutexb := 1; }
	count := count - 1;
	count := count + 1;
	atomic { assume mutexb == 1; mutexb := 0; }
  }
}

procedure ULTIMATE.start() returns()
modifies mutexa, mutexb, count;
{
  count := 0;
  mutexa := 0;
  mutexb := 0;
  
  fork 0 thread1();
  while (true) {
    fork 0 thread2();
  }
}