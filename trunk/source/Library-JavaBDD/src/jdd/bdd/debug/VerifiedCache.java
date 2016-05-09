package jdd.bdd.debug;


import jdd.bdd.*;
import jdd.util.*;
import jdd.util.math.*;

import java.util.*;


/**
 * This cache verifis the SimpleCache on the fly by testing it against an ideal cache.
 *
 * it is used by the developers to find bugs in the complex SimpleCache/OptimizedCache
 * classes. should not be used by users
 *
 * @see IdealCache
 * @see SimpleCache
 */




/* package */ public final class VerifiedCache extends CacheBase {
	private SimpleCache cache;
	private IdealCache ideal;

	// --------------------------------------------------------------------
	public int answer, hash_value;
	public VerifiedCache(String name, int size, int members, int bdds) {
		super(name);

		this.cache = new SimpleCache(name, size, members, bdds);
		this.ideal = new IdealCache(name, size, members, bdds);

	}


	/** current size of the cache */
	public int getSize() { return cache.getSize(); }

	// ---[ these operations just clean the cache ] ---------------------------------

	/** just wipe the cache */
	public void invalidate_cache() {
		cache.invalidate_cache();
		ideal.invalidate_cache();
	}

	public void free_or_grow() {
		cache.free_or_grow();
		ideal.free_or_grow();
	}
	public void free_or_grow(NodeTable nt) {
		cache.free_or_grow(nt);
		ideal.free_or_grow(nt);
	}
	public void invalidate_cache(NodeTable nt) {
		cache.invalidate_cache(nt);
		ideal.invalidate_cache(nt);
	}


	// -----------------------------------------------------------------------------


	public void insert(int hash, int key1, int value) {
		if(ideal.lookup(key1)) Test.checkEquality(value, ideal.answer, "Inserted value already exists but is inconsistent (1)");

		cache.insert(hash,key1, value);
		ideal.insert(hash,key1, value);
	}


	public void insert(int hash, int key1, int key2, int value) {
		if(ideal.lookup(key1, key2)) Test.checkEquality(value, ideal.answer, "Inserted value already exists but is inconsistent (2)");

		cache.insert(hash,key1, key2, value);
		ideal.insert(hash,key1, key2, value);
	}


	public void insert(int hash, int key1, int key2, int key3, int value) {
		if(ideal.lookup(key1, key2, key3)) Test.checkEquality(value, ideal.answer, "Inserted value already exists but is inconsistent (3)");

		cache.insert(hash,key1, key2, key3, value);
		ideal.insert(hash,key1, key2, key3, value);
	}

	// -----------------------------------------------------------
	public final boolean lookup(int a) {
		if( cache.lookup(a) ) {
			Test.check(ideal.lookup(a), "ideal cache not superset of cache (1)");
			Test.checkEquality(ideal.answer, cache.answer, "ideal cache and cache returning different answers (2)");
			answer = cache.answer;
			return true;
		}
		hash_value = cache.hash_value;
		return false;
	}

	public final boolean lookup(int a, int b) {
		if(cache.lookup(a,b)) {
			Test.check(ideal.lookup(a, b), "ideal cache not superset of cache (2)");
			Test.checkEquality(ideal.answer, cache.answer, "ideal cache and cache returning different answers (2)");
			answer = cache.answer;
			return true;
		}
		hash_value = cache.hash_value;
		return false;
	}



	public final boolean lookup(int a, int b, int c) {
	if(cache.lookup(a,b,c)) {
			Test.check(ideal.lookup(a,b,c), "ideal cache not superset of cache (3)");
			Test.checkEquality(ideal.answer, cache.answer, "ideal cache and cache returning different answers (3)");
			answer = cache.answer;
			return true;
		}
		hash_value = cache.hash_value;
		return false;
	}

	// -----------------------------------------------------------------------------

	public double computeLoadFactor() { return cache.computeLoadFactor(); }
	public double computeHitRate() { return cache.computeHitRate(); }
	public long getAccessCount() { return cache.getAccessCount(); }
	public int getCacheSize() { return cache.getCacheSize(); }
	public int getNumberOfClears() { return cache.getNumberOfClears(); }
	public int getNumberOfPartialClears() { return cache.getNumberOfPartialClears(); }
	public int getNumberOfGrows() { return cache.getNumberOfGrows(); }
	public void check_cache(NodeTable nt) { cache.check_cache(nt); }

	// --------------------------------------------------------------

	public void showStats() {
		JDDConsole.out.print("IDEAL:"); ideal.showStats();
		JDDConsole.out.print("NORMAL:"); cache.showStats();
	}


	// ----------------------------------------------------------------

	public static void main(String [] args) {
		// XXX: no test yet
	}

}
