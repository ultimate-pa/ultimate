package jdd.util.math;

import jdd.util.*;

/**
 * prime-number support, mostly used in the hash-tables
 * <p>
 * note: we consider zero to not be a prime :(
 */
public final class Prime {

	private static final int NUM_TRIALS = 8;

	private static final long witness(long a, long i, long n) {
		if(i == 0) return 1;
		long x = witness( a, i /2, n);
		if(x == 0) return 0;
		long y = (x * x) % n;
		if( y == 1 && x != 1 && x != n -1) return 0;
		if( (i %2) == 1) y = (a * y) % n;
		return y;
	}

	/**
	 * prime test
	 * @return true if "n" is a prime number
	 */
	public static final boolean isPrime(int n) {
		// small primes ?
		if(n < 20) {
			if( (n == 1) || (n == 2) || (n == 3) || (n == 5) || (n == 7) || (n == 11) || (n == 13) || (n == 17) || (n == 19))
				return true;
		}

		// multiple of small primes?
		if(( (n % 2) == 0)||  ( (n % 3) == 0)||  ( (n % 5) == 0)||  ( (n % 7) == 0)||  ( (n % 11) == 0)||  ( (n % 13) == 0)||  ( (n % 17) == 0)||  ( (n % 19) == 0))
			return false;

		// ... not? take out the big guns now:
		for(int c = 0; c < NUM_TRIALS; c++)
			if( witness( 2 + (long)( Math.random() * (n -2)), n-1, n) != 1)
				return false;

		// yes sir, we have a winner
		return true;
	}

	/**
	 * get the closest prime larger than "n", including "n" itself
	 */
	public static final int nextPrime(int n) {
		if( (n % 2) == 0) n++;
		for(;;) {
			if(isPrime(n)) return n;
			n += 2;
		}
	}


	/**
	 * get the closest prime smaller than "n", including "n" itself
	 */
	public static final int prevPrime(int n) {
		if( (n % 2) == 0) n--;
		for(;;) {
			if(isPrime(n)) return n;
			n -= 2;
		}
	}


	// ------------------------- [ testbed starts here ] --------------------------------
	private static boolean dumb_prime_check(int n) {
		int n0 = (int) Math.sqrt(n);
		if(n == 0) return false;
		if(n == 1) return true;
		for(int i = 2; i <= n0; i++) if( (n % i) == 0) return false;
		return true;
	}
	private static int dumb_next_prime(int n) {
		for(;;) if(dumb_prime_check(n)) return n; else n++;
	}


	/** testbench. do not call */
	public static void internal_test() {
		Test.start("Prime");

		Test.check( isPrime(1), "1 is prime");
		Test.check( isPrime(2), "2 is prime");
		Test.check( isPrime(3), "3 is prime");
		Test.check(!isPrime(4), "4 is NOT prime");
		Test.check( isPrime(5), "5 is prime");
		Test.check(!isPrime(6), "6 is NOT prime");
		Test.check( isPrime(7), "7 is prime");
		Test.check(!isPrime(8), "8 is NOT prime");
		Test.check(!isPrime(256), "256 is NOT prime");
		Test.check(!isPrime(13221), "13221 is NOTprime");

		// check isPrime
		boolean failed = false;
		for(int i = 0; !failed && i < 3000; i++) {
			int n = (int)(Math.random() * 1234567);
			if( isPrime(n) != dumb_prime_check(n)) failed = true;
		}
		Test.check(!failed, "isPrime failed");

		// now check nextPrime
		for(int i = 0; !failed && i < 3000; i++) {
			int n = (int)(Math.random() * 1234567);
			if(nextPrime(n) != dumb_next_prime(n)) failed = true;
		}
		Test.check(!failed, "nextPrime failed");

		Test.end();
	}
}
