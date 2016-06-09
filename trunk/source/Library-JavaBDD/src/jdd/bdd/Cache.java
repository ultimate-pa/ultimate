package jdd.bdd;

import jdd.util.Configuration;
import jdd.util.JDDConsole;
import jdd.util.Test;
import jdd.util.math.Digits;
import jdd.util.math.HashFunctions;


// DONE: add a ref-count for entries so we dont remove the most useds
// DONE: let cache_size be a power of two and use bitwise AND instead of MOD

/**
 * A cache :)
 * This is the old operation-cache used in JDD. it is being replaced with SimpleCache.java
 * that is somehow simpler (in its implementation) and saves a byte or two in memory...
 */

public final class Cache {
	private CacheEntry [] entries;
	private int cache_bits, cache_size, cache_mask;
	private long numaccess;
	private final long last_access;
	private int numclears, numpartial_clears;
	private final int members;
	private int numgrows;
	private int possible_bins_count;

	// private int numcols, numinserts, cache_hits, cache_misses;

	public Cache(int size, int members) {
		Test.check(members >= 1, "Cache members must be greater than 0");
		Test.check(members <= 3, "Cache members must be less than 4");

		cache_bits = (size < 32) ? 5 : Digits.closest_log2(size); // min size 32
		cache_size = (1 << cache_bits);
		cache_mask = cache_size -1;
		this.members = members;
		numgrows = 0;
		last_access = numaccess = 0;
		possible_bins_count = 0;
		numclears =  numpartial_clears = 0;

		entries = new CacheEntry[cache_size];
		for(int i = 0; i < cache_size; i++) {
			entries[i] = new CacheEntry();
		}
	}


	public int getSize() { return cache_size; }



	// ----[ these NOT will erase the cache entries that are still valid in node-tanle ] --------------

	public void invalidate_cache(NodeTable nt) {
		invalidate_cache(nt, cache_size);
	}

	// we used to have 'public void invalidate_cache(NodeTable nt)', but that turned out to be FAR solver
	// seince the bounde-checking on t_var could not be moved out of loop (or something like that?)...
	public void invalidate_cache(NodeTable nt, int size) {

		if(possible_bins_count == 0) {
			return;
		}
		numpartial_clears++;

		int ok = 0;
		if(members == 1) {
			for(int i = 0; i < size; i++) {
				if( !entries[i].invalid()) {
					if( !nt.isValid( entries[i].op1) ||  nt.isValid( entries[i].ret) ) {
						entries[i].clear();
					} else {
						ok++;
					}
				}
			}
		} else {
			for(int i = 0; i < size; i++) {
				if( !entries[i].invalid()) {
					if( !nt.isValid( entries[i].op1)  ||  !nt.isValid(entries[i].op2)  ||  !nt.isValid(entries[i].ret) ) {
						entries[i].clear();
					} else {
						ok++;
					}
				}
			}
		}
		if(ok == 0) {
			possible_bins_count = 0;
		}
	}

	public void free_or_grow(NodeTable nt) {
		if(numgrows < Configuration.maxCacheGrows) {
			if(computeLoadFactor() > Configuration.minCacheLoadfactorToGrow) {
				grow_and_invalidate_cache(nt);
				return;
			}
		}
		invalidate_cache(nt, cache_size);
	}
	/** grow the cache and invalidate everything [since the hash function hash chagned] */
	private void grow_and_invalidate_cache(NodeTable nt) {
		cache_bits++;
		final int size = 1 << cache_bits;
		cache_mask = size - 1;

		numgrows++;
		final CacheEntry [] tmp = new CacheEntry[size];
		for(int i = 0; i < cache_size; i++) {
			tmp[i] = entries[i];
		}
		invalidate_cache(nt, cache_size);

		for(int i = cache_size; i < size; i++) {
			tmp[i]  = new CacheEntry();
		}

		cache_size = size;
		entries = tmp;
	}

	// --[ these will erase the cache ] --------------------------------------------

	/* just wipe the cache */
	public void invalidate_cache() {
		if(possible_bins_count == 0) {
			return;
		}
		numclears++;

		for(int i = 0; i < cache_size; i++) {
			entries[i].clear();
		}
		possible_bins_count = 0;
	}

	public void free_or_grow() {
		if(numgrows < Configuration.maxCacheGrows) {
			if(computeLoadFactor() > Configuration.minCacheLoadfactorToGrow) {
				grow_and_invalidate_cache();
				return;
			}
		}
		invalidate_cache();
	}

	/** grow the cache and invalidate everything [since the hash function hash chagned] */
	private void grow_and_invalidate_cache() {
		cache_bits++;
		final int size = 1 << cache_bits;
		cache_mask = size - 1;


		numgrows++;
		final CacheEntry [] tmp = new CacheEntry[size];
		for(int i = 0; i < cache_size; i++){
			tmp[i] = entries[i];
			tmp[i].clear();
		}
		for(int i = cache_size; i < size; i++) {
			tmp[i]  = new CacheEntry();
		}
		cache_size = size;
		entries = tmp;
	}
	// --------------------------------------------------------------------------------
	//
	private static final int pair(int i, int j) {
		return ((i + j) * (i + j + 1) / 2 + i);
	}


	private final int hash1(int a) {
		return a & cache_mask;
	}


	private final int hash2(int a, int b) {
		return HashFunctions.hash_prime(a, b) & cache_mask;
	}

	private final int hash3(int  a, int b, int c) {
		return HashFunctions.hash_prime(a,b,c) & cache_mask;
	}

	// -------------------------------------------------------------------


	public CacheEntry access3(int type, int op1, int op2) {
		numaccess++;
		possible_bins_count++;
		return entries[ hash3(type, op1,op2)];
	}

	public CacheEntry access2(int op1, int op2) {
		numaccess++;
		possible_bins_count++;
		return entries[hash2(op1, op2) ];
	}

	public CacheEntry access1(int x ) {
		numaccess++;
		possible_bins_count++;
		return entries[x & cache_mask];
	}


	// ------------------------------ private helpers for the tests
	private void insert3(byte type, int op1, int op2, int answer) {
		final CacheEntry ce = access3(type, op1, op2);
		ce.type = type;
		ce.op1 = op1;
		ce.op2 = op2;
		ce.ret = answer;
	}

	private void insert2(byte type, int op, int answer) {
		final CacheEntry ce = access2(type, op);
		ce.type = type;
		ce.op1  = op;
		ce.ret  = answer;
	}
	private  void insert1(int op, int answer) {
		final CacheEntry ce = access1( op);
		ce.op1  = op;
		ce.ret  = answer;
	}


	private int lookup3(byte type, int op1, int op2) {
		final CacheEntry ce = access3(type, op1, op2);
		return (ce.op1 == op1 && ce.op2 == op2 && ce.type == type) ? ce.ret : -1;
	}

	private int lookup2(byte type, int op) {
		final CacheEntry ce = access2(type, op);
		return (ce.op1 == op && ce.type == type) ? ce.ret : -1;
	}
	private int lookup1( int op) {
		final CacheEntry ce = access1(op);
		return (ce.op1 == op) ? ce.ret : -1;
	}



	// ------------------------------------------------------
	/** cache load factor, slow! */
	public double computeLoadFactor() { // just see howmany buckts are in use
		int bins = 0;
		for( int i = 0; i < cache_size; i++) {
			if(!entries[i].invalid() ) {
				bins++;
			}
		}
		return (bins * 10000 / cache_size) / 100.0;
	}

	/* hit-rate since the last clear */
	public double computeHitRate() {
		long hits = 0;
		for( int i = 0; i < cache_size; i++) {
			hits +=  entries[i].found;
		}
		return ((int)( (hits * 10000) / ( numaccess ))) / 100.0;
	}

	// public int getHitRate() { return (cache_hits + cache_misses) > 0 ? 100 * cache_hits / (cache_hits + cache_misses) : 0; }
	// public int getCollisionRate() {return (numinserts) > 0 ? 100 * numcols / (numinserts) : 0;}

	public void showStats(String type) {
		if(numaccess != 0) {
			JDDConsole.out.print(type + "-cache ");
			JDDConsole.out.print("ld=" + computeLoadFactor() + "% ");
			JDDConsole.out.print("sz="); 	Digits.printNumber(cache_size);

			JDDConsole.out.print("accs=");	Digits.printNumber(numaccess);
			JDDConsole.out.print("clrs=" + numclears+ "/" + numpartial_clears + " ");

			JDDConsole.out.print("hitr=" + computeHitRate() + "% ");
			if(numgrows > 0) {
				JDDConsole.out.print("grws=" + numgrows + " ");
			}


			showDeviation();
			JDDConsole.out.println();
		}
	}

	private void showDeviation() {
		double mean = 0.0, meansq = 0.0;
		int max = 0, min = Integer.MAX_VALUE, used = 0;
		for( int i = 0; i < cache_size; i++) {
			final int x = entries[i].found;
			if(x > 0) {
				used++;
			}
			mean += x;
			meansq +=  x * x;
			max = Math.max( entries[i].overwrite, max);
			min = Math.min( entries[i].overwrite, min);
		}
		mean /= cache_size;
		meansq /= cache_size;

		final double stddev = Math.sqrt( meansq  - mean * mean);
		final double e_stddev = Math.sqrt(( 1.0 - 1.0 / cache_size) * numaccess / cache_size);
		JDDConsole.out.print("use/exp=" + (100 * used / cache_size) + "/" +
			(int)(100 * (1 - Math.pow(Math.E, -mean))) + "%");

		// JDDConsole.out.print("\nmin=" + min + ", max = " + max);
	}


	/** check if a cached answer is a valid node. ONLY VALID FOR BDD-ANSWER CACHES! */
	public void check_cache(int [] t_var) {
		for( int i = 0; i < cache_size; i++) {
			if(!entries[i].invalid()) {
				if(t_var[ entries[i].ret] <0) {
					JDDConsole.out.println("Invalied cache entry at position " + i);
					JDDConsole.out.println("" + i + " --> " +  entries[i].op1 + "/" +  entries[i].op2 + "/"+ entries[i].ret + "  " +  entries[i].type);
					System.exit(20);
				}
			}
		}
	}
	// --------------------------- misc

	/* package */ void show_cache() {

		for(int i = 0; i < cache_size; i++) {
			if(!entries[i].invalid() ) {
				switch(members) {
					case 1:
						JDDConsole.out.println("" + i + " --> " + entries[i].op1 + "/"+  entries[i].ret);
						break;
					case 2:
						JDDConsole.out.println("" + i + " --> " +  entries[i].op1 + "/"+  entries[i].ret + "  " +  entries[i].type);
						break;
					case 3:
						JDDConsole.out.println("" + i + " --> " +  entries[i].op1 + "/" +  entries[i].op2 + "/"+ entries[i].ret + "  " +  entries[i].type);
						break;
				}
			}
		}

	}

	/** runs some statistic tests on the hash functions ... */
	/** testbench. do not call */
	public static void internal_test() {

		Test.start("Cache");

		// 3 elements
		Cache cache = new Cache(200, 3);

		cache.insert3((byte)2, 1,2,3);
		Test.check( cache.lookup3((byte) 2,1,2) == 3, "lookup 3");
		cache.insert3((byte)2, 1,2,5);
		Test.check( cache.lookup3((byte) 2,1,2) == 5, "lookup overwritten with 5");
		Test.check( cache.lookup3((byte) 1,1,2) == -1, "non-existing entry 1");
		Test.check( cache.lookup3((byte) 2,2,2) == -1, "non-existing entry 2");
		Test.check( cache.lookup3((byte) 2,2,1) == -1, "non-existing entry 3");



		// 2 elements
		cache = new Cache(200, 2);

		cache.insert2((byte)2, 1,3);
		Test.check( cache.lookup2((byte) 2,1) == 3, "lookup 3");
		cache.insert2((byte)2, 1,5);
		Test.check( cache.lookup2((byte) 2,1) == 5, "lookup overwritten with 5");
		Test.check( cache.lookup2((byte) 1,1) == -1, "non-existing entry 1");
		Test.check( cache.lookup2((byte) 2,2) == -1, "non-existing entry 2");



		// 1 element
		cache = new Cache(200, 1);

		cache.insert1(1,3);
		Test.check( cache.lookup1(1) == 3, "lookup 3");
		cache.insert1(1,5);
		Test.check( cache.lookup1(1) == 5, "lookup overwritten with 5");
		Test.check( cache.lookup1(2) == -1, "non-existing entry 1");
		Test.check( cache.lookup1(3) == -1, "non-existing entry 2");


		Test.end();

	}
}
