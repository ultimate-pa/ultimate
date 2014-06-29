/*
 * Program from Fig.1 of
 * 2002POPL - Henzinger,Jhala,Majumdar,Sutre - Lazy abstraction
 * 
 * Date: 2014-06-28
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * 
 *
 */
extern int __VERIFIER_nondet_int(void);

int LOCK;

void lock(void) {
	if (LOCK == 0) {
		LOCK = 1;
	} else {
		// assert \false;
	}
}

void unlock(void) {
	if (LOCK == 1) {
		LOCK = 0;
	} else {
		// assert \false;
	}
}

int main() {
	int got_lock;
	int old = 0, new = 0;
	if (__VERIFIER_nondet_int()) {
		do {
			got_lock = 0;
			if (__VERIFIER_nondet_int()) {
				lock();
				got_lock++;
			}
			if (got_lock) {
				unlock();
			}
		} while (__VERIFIER_nondet_int());
	}
	do {
		lock();
		old = new;
		if (__VERIFIER_nondet_int()) {
			unlock();
			new++;
		}
	} while (new != old);
	unlock();
	return 0;
}

