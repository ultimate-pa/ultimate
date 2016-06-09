



package jdd.internal.tests;

import jdd.util.JDDConsole;
import jdd.util.Options;
import jdd.util.Test;

/**
 * test calls are invoked from here.
 *
 */

public class RunTests {

	public static void internal_test() {
		// TODO
	}

	// ------------------------------------

	public static void main(String [] args) {

		// dont have time for this kinda stuff:
		Options.profile_cache = false;
		Options.verbose = false;

		try {

			// first, my own tests:
			RunTests.internal_test();


			// most used utilities here
			jdd.util.Array.internal_test();
			jdd.util.Flags.internal_test();


			// math utils
			jdd.util.math.Prime.internal_test();
			jdd.util.math.Digits.internal_test();
			jdd.util.math.FastRandom.internal_test();
			jdd.util.math.HashFunctions.internal_test();

			// BDDs, yikes!
			jdd.bdd.NodeTable.internal_test();
			/// REMOVED jdd.bdd.NodeHT.internal_test();
			// jdd.bdd.Cache.internal_test();
			jdd.bdd.SimpleCache.internal_test();
			jdd.bdd.OptimizedCache.internal_test();
			jdd.bdd.DoubleCache.internal_test();
			jdd.bdd.BDD.internal_test();
			jdd.bdd.BDDIO.internal_test();

			// Quasi-reduced BDDs (not finished yet)
			// jdd.qbdd.QBDD.internal_test();


			// Zero-supressed BDDs
			jdd.zdd.ZDD.internal_test();
			jdd.zdd.ZDD2.internal_test();
			jdd.zdd.ZDDGraph.internal_test();
			jdd.zdd.ZDDCSP.internal_test();


			// the examples are used as tests too :(
			jdd.examples.BDDQueens.internal_test();
			jdd.examples.ZDDQueens.internal_test();
			jdd.examples.ZDDCSPQueens.internal_test();


			// BDD sets
			jdd.bdd.sets.BDDUniverse.internal_test();
			jdd.bdd.sets.BDDSet.internal_test();



			// *** hurrayy, we did it ***
			JDDConsole.out.println("\nALL " + Test.total + " TESTS WERE SUCCESSFUL!");
		} catch(final Throwable exx) {
			exx.printStackTrace();
		}

	}
}
