

// XXX:	if you improve/correct anything here, you mightwant to change DoubleCache too!!

// XXX: todo: we need a more soft MAX_HITRATE, that is, if the load-rate is very high,
//            then we should allow even a hitrate about 30-35% to trigger a grow!

// XXX: our good_hash() is not that good :(


package jdd.bdd;

import jdd.util.Allocator;
import jdd.util.Configuration;
import jdd.util.JDDConsole;
import jdd.util.Options;
import jdd.util.Test;
import jdd.util.math.Digits;
import jdd.util.math.HashFunctions;
import jdd.util.math.Prime;


/**
 * A cache class that is [we belive] faster and uses less memory than Cache.java.
 *
 * @see Cache
 * @see DoubleCache
 * @see OptimizedCache
 */



// The new SimpleCache works like this:
//
// since the caches may become very large, we use a sequential representation of nodes
// to minimize CPU cache problems.
//
// all cache entries are gathered in "data". each cache entry occupies "width" integers
// - the first element is always the output
// - next element is the first input value and so on.
// so an entry (a,b,c) => x is represented as [x, a, b, c] in data.
// to avoid to much low-level code, users should use the helper functions:
// getIn(), getOut(), setIn(), setOut(), isInvalid(), invalidate()

public class SimpleCache extends CacheBase {
	private int []data;

	public int answer, hash_value;

	private int cache_bits, shift_bits, cache_mask;
	protected int members, width, bdds, numclears, numgrows, cache_size;
	protected long numaccess;
	protected long hit, miss, last_hit, last_access; // cache hits and misses, hit/acces-count since last grow

	/**
	 * the arguments are:
	 * (size of elements, number of members. number of members that also are BDD nodes)
	 */
	public SimpleCache(String name, int size, int members, int bdds) {
		super(name);

		if(size < Configuration.MIN_CACHE_SIZE) {
			size = Configuration.MIN_CACHE_SIZE;
		}

		this.members = members;
		width   = members + 1; // plus one for the output
		this.bdds    = bdds;
		cache_bits = Digits.closest_log2(size); // min size 32
		shift_bits = 32 - cache_bits; // w-n, where w is the machine word size..
		cache_size = (1 << cache_bits);
		cache_mask = cache_size -1;

		numgrows = 0;
		numaccess = 0;
		hit = miss = last_hit = last_access = 0;

		numclears = 0;

		cache_size = Prime.nextPrime(cache_size); // NEW: cache size is prime
		data = Allocator.allocateIntArray(cache_size * width);
		clear_cache();
	}

	// ---------------------------------------------------------------
	// low level access
	protected final int getOut(int i) {	return data[i * width]; }
	protected final void setOut(int i, int v) { 	data[i * width] = v; }

	protected final int getIn(int i, int member) {	return data[i * width + member]; }
	protected final void setIn(int i, int member, int v) { 	data[i * width + member] = v; }


	/** invalidate the complete cache */
	protected final void clear_cache() {
		for(int i = cache_size; i != 0; ) {
			invalidate(--i);
		}
	}

	protected final void invalidate(int number) {		setIn(number, 1, -1); }
	protected final boolean isValid(int number) {		return getIn(number, 1)  != -1;	}

	// -------------------------------------------------------------------

	/* return the amount of internally allocated memory in bytes */
	public long getMemoryUsage() {
		long ret = 0;
		if (data != null) {
			ret += data.length * 4;
		}
		return ret;
	}

	/** the _real_ size of the cache. it is probably higher than what the user requested */
	public int getSize() { return cache_size; }

	/**
	 * see if we are allowed to grow this cache.
	 * We grow the cache if (numgrows < MAX_SIMPLECACHE_GROWS) and the hit-rate since the last
	 * grow is larger than MIN_SIMPLECACHE_HITRATE_TO_GROW.
	 *
	 */

	protected boolean may_grow() {
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
		clear_cache();
		numclears++;
	}


	/** try to grow the cache. if unable, it will just wipe the cache clean */
	public void free_or_grow() {
		if(may_grow()) {
			grow_and_invalidate_cache();
		} else {
			invalidate_cache();
		}
	}


	/** grow the cache and invalidate everything [since the hash function hash chagned] */
	protected void grow_and_invalidate_cache() {
		cache_bits++;
		shift_bits--;
		cache_size = 1 << cache_bits;
		cache_size = Prime.nextPrime(cache_size); // NEW: cache size is prime
		cache_mask = cache_size - 1;

		data = null;	data= Allocator.allocateIntArray(cache_size * width);

		if(Options.verbose) {
			JDDConsole.out.println("Cache " + getName() + " grown to " + cache_size + " entries");
		}

		// clear the cache
		invalidate_cache();
	}

	// ---[ these operations clean only invalid nodes ] ----------------------

	/**
	 * either _partially_ wipe the cache or try to grow it.
	 *
	 * XXX: at the moment, if cache is grown all current data is lost
	 *
	 * @see #free_or_grow
	 */
	public void free_or_grow(NodeTable nt) {
		if(may_grow()) {
			grow_and_invalidate_cache(); // no way to partially invalidate, as the size and thus the hashes chagnes
		} else {
			invalidate_cache(nt);
		}
	}

	/**
	 * removes the elements that are garbage collected.
	 * this is where the "bdds" variable in constructor is used.
	 */
	public void invalidate_cache(NodeTable nt) {
		invalidate_cache(); // no optimization here
	}


	// -----------------------------------------------------------------------------


	/** this is the _correct_ way to insert something into the cache. format: (key1->value)  */
	public void insert(int hash, int key1, int value) {
		setOut(hash, value);
		setIn(hash, 1, key1);
	}

	/** this is the _correct_ way to insert something into the cache. format: (key1,key2->value)  */
	public void insert(int hash, int key1, int key2, int value) {
		setOut(hash, value);
		setIn(hash, 1, key1);
		setIn(hash, 2, key2);
	}

	/** this is the _correct_ way to insert something into the cache. format: (key1,key2,key3->value)  */
	public void insert(int hash, int key1, int key2, int key3, int value) {
		setOut(hash, value);
		setIn(hash, 1, key1);
		setIn(hash, 2, key2);
		setIn(hash, 3, key3);
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
		numaccess++;
		final int hash = good_hash(a);
		if(getIn(hash, 1)  == a){
			hit++;
			answer = getOut(hash);
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
		numaccess++;
		final int hash = good_hash(a,b);
		if( getIn(hash, 1) == a && getIn(hash, 2) == b) {
			hit++;
			answer = getOut(hash);
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
		numaccess++;
		final int hash = good_hash(a,b,c);
		if(  getIn(hash, 1) == a && getIn(hash, 2) == b && getIn(hash, 3) == c ) {
			hit++;
			answer = getOut(hash);
			return true;
		} else {
			miss++;
			hash_value = hash;
			return false;
		}
	}



	// -----[ the HASH functions ] -------------------------


	protected final int good_hash(int i) {
		// return HashFunctions.mix(i) & cache_mask;
		// NEW: cache size is prime
		return i % cache_size;
	}

	protected final int good_hash(int i, int j) {
		 // return HashFunctions.mix(HashFunctions.hash_prime(i,j)) & cache_mask;
		 // NEW: cache size is prime
		 return (HashFunctions.hash_prime(i,j) & 0x7FFFFFFF)% cache_size;
	}
	protected final int good_hash(int i, int j, int k) {
		// return HashFunctions.hash_prime(i,j,k) & cache_mask;
		// return HashFunctions.limit_mix_masked( HashFunctions.hash_prime(i,j,k), cache_mask);
		// return HashFunctions.mix( HashFunctions.hash_prime(i,j,k)) &  cache_mask;
		// NEW: cache size is prime
		return (HashFunctions.hash_prime(i,j,k) & 0x7FFFFFFF) % cache_size;
	}


	// -----------------------------------------------------------------------------

	@Override
	public double computeLoadFactor() { // just see howmany buckts are in use
		if(data == null)
		 {
			return 0; // is growing...
		}

		int bins = 0;
		for( int i = 0; i < cache_size; i++) {
			if(isValid(i)) {
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
			JDDConsole.out.print("sz="); Digits.printNumber1024(cache_size);
			JDDConsole.out.print("accs="); Digits.printNumber1024(numaccess);
			JDDConsole.out.print("clrs=" + numclears+ "/0 ");
			JDDConsole.out.print("hitr=" + computeHitRate() + "% ");
			if(numgrows > 0) {
				JDDConsole.out.print("grws=" + numgrows + " ");
			}

			JDDConsole.out.println();
		}
	}
	public void show_tuple(int bdd) {
		JDDConsole.out.print(""  + bdd + ":   " + getOut(bdd));
		for(int i = 0; i < members; i++) {
			JDDConsole.out.print("\t" + getIn(bdd, 1 + i) );
		}
		JDDConsole.out.println();
	}

	// XXX: other BDD members not checked yet...

	public void check_cache(NodeTable nt) {
		for( int i = 0; i < cache_size; i++) {
			if( isValid(i)) {

				if(! nt.isValid( getOut(i) ) ) {
					JDDConsole.out.println("Invalied cache output entry");
					show_tuple(i);
					System.exit(20);
				}

				for(int m = 0; m < bdds; m++) {
					if(! nt.isValid( getIn(i, m + 1)) ) {
						JDDConsole.out.println("Invalied cache member " + m + " entry");
						show_tuple(i);
						System.exit(20);
					}
				}

			}
		}
	}

	// ----------------------------------------------------------------

	/** testbench. do not call */
	public static void internal_test() {
		// SimpleCache testbench, more or less ripped from Cache.java...

		Test.start("SimpleCache");

		// 3 elements
		SimpleCache cache = new SimpleCache("test", 200, 3,3);

		cache.add(2, 1,2,3);

		Test.check( cache.lookup( 2,1,2) && cache.answer == 3, "lookup 3");
		cache.add(2, 1,2,5);
		Test.check( cache.lookup( 2,1,2) && cache.answer == 5, "lookup overwritten with 5");
		Test.check( !cache.lookup( 1,1,2), "non-existing entry 1");
		Test.check( !cache.lookup( 2,2,2), "non-existing entry 2");
		Test.check( !cache.lookup( 2,2,1), "non-existing entry 3");



		// 2 elements
		cache = new SimpleCache("test", 200, 2,2);

		cache.add(2, 1,3);
		Test.check( cache.lookup( 2,1) && cache.answer == 3, "lookup 3");
		cache.add(2, 1,5);
		Test.check( cache.lookup( 2,1) && cache.answer == 5, "lookup overwritten with 5");
		Test.check( !cache.lookup( 1,1), "non-existing entry 1");
		Test.check( !cache.lookup( 2,2), "non-existing entry 2");



		// 1 element
		cache = new SimpleCache("test", 200, 1,1);

		cache.add(1,3);
		Test.check( cache.lookup(1) && cache.answer == 3, "lookup 3");
		cache.add(1,5);
		Test.check( cache.lookup(1) && cache.answer == 5, "lookup overwritten with 5");
		Test.check( !cache.lookup(2), "non-existing entry 1");
		Test.check( !cache.lookup(3), "non-existing entry 2");

		Test.end();

	}

}
