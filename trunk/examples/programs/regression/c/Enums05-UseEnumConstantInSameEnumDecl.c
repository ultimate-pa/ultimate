//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2018-09-01
// Enumm declaration from the pthreads library.
// A just defined enumeration constant is used 
// as a value in the very same declaration.

enum
{
  PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_ADAPTIVE_NP
  ,
  PTHREAD_MUTEX_NORMAL = PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE = PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK = PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_DEFAULT = PTHREAD_MUTEX_NORMAL
};

int main() {
	if (PTHREAD_MUTEX_TIMED_NP != PTHREAD_MUTEX_TIMED_NP) {
		//@ assert \false;
	}
	return 0;
}
