

package jdd.bdd.debug;

import jdd.bdd.CacheBase;
import jdd.util.Allocator;
import jdd.util.Array;
import jdd.util.Configuration;
import jdd.util.JDDConsole;
import jdd.util.math.Digits;

/**
 * RandomCache.java:
 *
 * like SimpleCache but used changing random numbers instead of large prime number
 * to distribute the hash value. may help to avoid weird situation when cache
 * is stuck in a local minima (kinda of).
 *
 * do not use, <b>for JDD developers only!!</b>
 */

/* package */ public final class RandomCache extends CacheBase {
	private int []in1, in2, in3, out;

	public int answer, hash_value;
	private int togo, p1, p2, p3;

	private int cache_bits, shift_bits, cache_size, cache_mask;
	private final int bdds;

	private int numclears;

	private int numgrows;
	private long  numaccess;
	private long hit,miss, last_hit, last_access; // cache hits and misses, hit/acces-count since last grow

	/**
	 * the arguments are:
	 * (size of elements, number of members. number of members that also are BDD nodes)
	 */
	public RandomCache(String name, int size, int members, int bdds) {
		super(name);

		this.bdds    = bdds;
		cache_bits = (size < 32) ? 5 : Digits.closest_log2(size); // min size 32
		shift_bits = 32 - cache_bits; // w-n, where w is the machine word size..
		cache_size = (1 << cache_bits);
		cache_mask = cache_size -1;

		numgrows = 0;
		numaccess = 0;
		hit = miss = last_hit = last_access = 0;

		numclears = 0;

		in1 = Allocator.allocateIntArray(cache_size);
		in2 = (members >= 2) ? Allocator.allocateIntArray(cache_size) : null;
		in3 = (members >= 3) ? Allocator.allocateIntArray(cache_size) : null;

		out= Allocator.allocateIntArray(cache_size);

		Array.set(in1, -1);
		update();
	}

	// ------------------------------------------------
	private void hash_check() {
		togo--;
		if(togo < 0) {
			update();
		}
	}
	private void update() {
		togo = 500000;
		p1 = (int)(10000000 * Math.random() );
		p2 = (int)(10000000 * Math.random() );
		p3 = (int)(10000000 * Math.random() );
		JDDConsole.out.println("hash update:" + p1 + "/" + p2 + "/" + p3);
	}

	/** the _real_ size of the cache. it is probably higher than what the user requested */
	public int getSize() { return cache_size; }

	/**
	 * see if we are allowed to grow this cache.
	 * We grow the cache if (numgrows < MAX_SIMPLECACHE_GROWS) and the hit-rate since the last
	 * grow is larger than MIN_SIMPLECACHE_HITRATE_TO_GROW.
	 *
	 */

	private boolean may_grow() {
		if(numgrows < Configuration.maxSimplecacheGrows) {
			final long acs = (numaccess - last_access);

			// only when we have "MIN_SIMPLECACHE_ACCESS_TO_GROW %" or more access', we have enough information to decide
			// whether we can grow cache or not (beside, if acs == 0, we will get a div by 0 below :)
			if( (acs * 100 )  < cache_size * Configuration.minSimplecacheAccessToGrow) {
				return false;
			}


			// compute hitrate (in procent) since the LAST grow, not the overall hitrate
			final int rate = (int)( ((hit - last_hit) * 100.0 ) / acs);

			if(rate > Configuration.minSimplecacheHitrateToGrow) {
				// store information needed to compute the next after-last-grow-hitrate
				last_hit = hit;
				last_access = numaccess;

				// register a grow and return true
				numgrows ++;
				return true;
			}
		}
		return false;
	}

	// ---[ these operations just clean the cache ] ---------------------------------

	/** just wipe the cache */
	public void invalidate_cache() {
		Array.set(in1, -1);
		numclears++;
	}


	/** try to grow the cache. if unable, it will just wipe the cache */
	public void free_or_grow() {
		if(may_grow()) {
			grow_and_invalidate_cache();
		} else {
			invalidate_cache();
		}
	}


	/** grow the cache and invalidate everything [since the hash function hash chagned] */
	private void grow_and_invalidate_cache() {
		cache_bits++;
		shift_bits--;
		cache_size = 1 << cache_bits;
		cache_mask = cache_size - 1;

		in1 = null;	in1 = Allocator.allocateIntArray(cache_size);
		out = null;	out = Allocator.allocateIntArray(cache_size);

		if(in2 != null) { in2 = null;	in2 = Allocator.allocateIntArray(cache_size); }
		if(in3 != null) { in3 = null;	in3 = Allocator.allocateIntArray(cache_size); }

		Array.set(in1, -1);
		numclears++;
	}

	// ---[ these operations clean only invalid nodes ] ----------------------

	/**
	 * either _partially_ wipe the cache or try to grow it.
	 *
	 * XXX: at the moment, if cache is grown all current data is lost
	 *
	 * @see #free_or_grow
	 */
	public void free_or_grow(int [] valid) {
		if(may_grow()) {
			grow_and_invalidate_cache(); // no way to partially invalidate, as the size and thus the hashes chagnes
		} else {
			invalidate_cache(valid);
		}
	}

	/**
	 * removes the elements that are garbage collected.
	 * this is where the "bdds" variable in constructor is used.
	 */
	public void invalidate_cache(int [] valid) {
		invalidate_cache(); // no optimization here
	}


	// -----------------------------------------------------------------------------


	/** this is the _correct_ way to insert something into the cache. format: (key1->value)  */
	public void insert(int hash, int key1, int value) {
		in1[hash] = key1;
		out[hash] = value;
	}

	/** this is the _correct_ way to insert something into the cache. format: (key1,key2->value)  */
	public void insert(int hash, int key1, int key2, int value) {
		in1[hash] = key1;
		in2[hash] = key2;
		out[hash] = value;
	}

	/** this is the _correct_ way to insert something into the cache. format: (key1,key2,key3->value)  */
	public void insert(int hash, int key1, int key2, int key3, int value) {
		in1[hash] = key1;
		in2[hash] = key2;
		in3[hash] = key3;
		out[hash] = value;
	}

	// -----------------------------------------------------------------------------
	/** just insert. this is for INTERNAL use only */
	/* package */ void add(int key1, int value) {
		insert( good_hash(key1), key1, value);
	}

	/** just insert. this is for INTERNAL use only */
	/* package */ void add(int key1, int key2, int value) {
		insert( good_hash(key1, key2), key1, key2, value);
	}

	/** just insert. this is for INTERNAL use only */
	/* package */ void add(int key1, int key2, int key3, int value) {
		insert( good_hash(key1, key2, key3), key1, key2, key3, value);
	}

	// -----------------------------------------------------------------------------

	/**
	 * lookup the element associated with (a)
	 * returns true if element found (stored in SimpleCache.answer)
	 * returns false if element not found. user should copy the hash value
	 * from SimpleCache.hash_value before doing any more cache-operations!
	 */
	public final boolean lookup(int a) {
		hash_check();


		numaccess++;
		final int hash = a & cache_mask;
		if(in1[hash] == a){
			hit++;
			answer = out[hash];
			return true;
		} else {
			miss++;
			hash_value = hash;
			return false;
		}
	}


	/**
	 * lookup the element associated with (a,b)
	 * returns true if element found (stored in SimpleCache.answer)
	 * returns false if element not found. user should copy the hash value
	 * from SimpleCache.hash_value before doing any more cache-operations!
	 */
	public final boolean lookup(int a, int b) {
		hash_check();


		numaccess++;
		final int hash = good_hash(a,b);
		if(in1[hash] == a && in2[hash] == b){
			hit++;
			answer = out[hash];
			return true;
		} else {
			miss++;
			hash_value = hash;
			return false;
		}
	}


	/**
	 * lookup the element associated with (a,b,c)
	 * returns true if element found (stored in SimpleCache.answer)
	 * returns false if element not found. user should copy the hash value
	 * from SimpleCache.hash_value before doing any more cache-operations!
	 */
	public final boolean lookup(int a, int b, int c) {
		hash_check();

		numaccess++;

		final int hash = good_hash(a,b,c);
		if(in1[hash] == a && in2[hash] == b && in3[hash] == c){
			hit++;
			answer = out[hash];
			return true;
		} else {
			miss++;
			hash_value = hash;
			return false;
		}
	}



	private final int good_hash(int i) {
		return (i  * p1) & cache_mask; // cant get much better ?
	}

	private final int good_hash(int i, int j) {
		 return ((i * p1 + j * p2) >>> shift_bits) & cache_mask;
	}
	private final int good_hash(int i, int j, int k) {
		 // return ((i * p1 + j * p2 + k * p3) >>> shift_bits) & cache_mask;
		 return (i * p1 + j * p2 + k * p3) & cache_mask;
	}


	// -----------------------------------------------------------------------------

	@Override
	public double computeLoadFactor() { // just see howmany buckts are in use
		if(in1 == null)
		 {
			return 0; // is growing...
		}

		int bins = 0;
		for( int i = 0; i < cache_size; i++) {
			if(in1[i] != -1 ) {
				bins++;
			}
		}
		return (bins * 10000 / cache_size) / 100.0;
	}

	@Override
	public double computeHitRate() { // hit-rate since the last clear
		if(numaccess == 0) {
			return 0;
		}
		return ((int)((hit * 10000) / ( numaccess ))) / 100.0;
	}

	@Override
	public long getAccessCount() {
		return numaccess;
	}

	@Override
	public int getCacheSize() {
		return cache_size;
	}

	@Override
	public int getNumberOfClears() {
		return numclears;
	}

	@Override
	public int getNumberOfPartialClears() {
		return 0;
	}

	@Override
	public int getNumberOfGrows() {
		return numgrows;
	}
	// --------------------------------------------------------------

	public void showStats() {
		if(numaccess != 0) {
			JDDConsole.out.print(getName() + "-cache ");
			JDDConsole.out.print("ld=" + computeLoadFactor() + "% ");
			JDDConsole.out.print("sz="); Digits.printNumber(cache_size);
			JDDConsole.out.print("accs="); Digits.printNumber(numaccess);
			JDDConsole.out.print("clrs=" + numclears+ "/0 ");
			JDDConsole.out.print("hitr=" + computeHitRate() + "% ");
			if(numgrows > 0) {
				JDDConsole.out.print("grws=" + numgrows + " ");
			}

			JDDConsole.out.println();
		}
	}

	// XXX: other BDD members not checked yet...
	public void check_cache(int [] t_var) {
		for( int i = 0; i < cache_size; i++) {
			if(in1[i] != -1) {
				if(t_var[ out[i]] == -1) {
					JDDConsole.out.println("Invalied cache entry at position " + i);
					JDDConsole.out.println("" + i + " --> " +  in1[i]+ "/" +  out[i]);
					showStats();
					System.exit(20);
				}
			}
		}
	}

}
