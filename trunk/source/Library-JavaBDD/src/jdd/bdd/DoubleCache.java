
package jdd.bdd;

import jdd.util.Allocator;
import jdd.util.Array;
import jdd.util.Configuration;
import jdd.util.JDDConsole;
import jdd.util.Test;
import jdd.util.math.Digits;

/**
 * Cache for int->double. based on simple cache
 *
 */

// XXX: todo: we need a more soft MAX_HITRATE, that is, if the load-rate is very high,
//            then we should allow even a hitrate about 30-35% to trigger a grow!

// XXX: our good_hash() is not that good :(

public final class DoubleCache extends CacheBase {
	private int []in;
	private double [] out;

	public int hash_value;
	public double answer;

	private int cache_bits, shift_bits, cache_size, cache_mask;
	private int possible_bins_count, numclears, numpartial_clears, numgrows;
	private long  numaccess, partial_count, partial_kept;
	private long hit,miss, last_hit, last_access; // cache hits and misses, hit/acces-count since last grow

	/**
	 * the arguments are:
	 * (size of elements, number of members. number of members that also are BDD nodes)
	 */
	public DoubleCache(String name, int size) {
		super(name);

		cache_bits = (size < 32) ? 5 : Digits.closest_log2(size); // min size 32
		shift_bits = 32 - cache_bits; // w-n, where w is the machine word size..
		cache_size = (1 << cache_bits);
		cache_mask = cache_size -1;

		numgrows = 0;
		numaccess = 0;
		hit = miss = last_hit = last_access = 0;
		partial_count = partial_kept= 0;

		possible_bins_count = 0;
		numclears =  numpartial_clears = 0;

		in = Allocator.allocateIntArray(cache_size);
		out = Allocator.allocateDoubleArray(cache_size);
		Array.set(in, -1);

	}


	/** the _real_ size of the cache. it is probably higher than what the user requested */
	public int getSize() { return cache_size; }

	/* return the amount of internally allocated memory in bytes */
	public long getMemoryUsage() {
		long ret = 0;
		if (in  != null) {
			ret += in.length * 4;
		}
		if (out != null) {
			ret += out.length * 4;
		}
		return ret;
	}

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
		Array.set(in, -1);
		possible_bins_count = 0;
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

		in= null;	in = Allocator.allocateIntArray(cache_size);
		out = null;	out = Allocator.allocateDoubleArray(cache_size);
		Array.set(in, -1);
		possible_bins_count = 0;
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
		if(possible_bins_count == 0) {
			return;
		}
		numpartial_clears++;

		int ok = 0;


		for(int i = 0; i < cache_size; i++) {
			if( in[i] == -1 || !nt.isValid( in[i]) ) {
				in[i] = -1;
			} else {
				ok++;
			}
		}

		partial_count += cache_size;	// for showStats
		partial_kept  += ok;			// for showStats
		possible_bins_count = ok;		// at this point ok = exact current bin-count
	}


	// -----------------------------------------------------------------------------


	/** this is the _correct_ way to insert something into the cache. format: (key1->value)  */
	public void insert(int hash, int key1, double value) {
		possible_bins_count++;
		in[hash] = key1;
		out[hash] = value;
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
		final int hash = a & cache_mask;
		if(in[hash] == a){
			hit++;
			answer = out[hash];
			return true;
		} else {
			miss++;
			hash_value = hash;
			return false;
		}
	}



	// -----[ HASH functions  ] -------------------------

	private final int good_hash(int i) {
		return i & cache_mask; // cant get much better ?
	}


	// -----------------------------------------------------------------------------

	@Override
	public double computeLoadFactor() { // just see howmany buckts are in use
		int bins = 0;
		for( int i = 0; i < cache_size; i++) {
			if(in[i] != -1 ) {
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
		return numpartial_clears;
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
			JDDConsole.out.print("clrs=" + numclears+ "/" + numpartial_clears + " ");

			JDDConsole.out.print("hitr=" + computeHitRate() + "% ");
			if(partial_count > 0) {
				final double pck = ((int)(10000.0 * partial_kept / partial_count)) / 100.0;
				JDDConsole.out.print("pck=" +  pck + "% ");
			}
			if(numgrows > 0) {
				JDDConsole.out.print("grws=" + numgrows + " ");
			}

			JDDConsole.out.println();
		}
	}


	// ----------------------------------------------------------------

	/** testbench. do not call */
	public static void internal_test() {
		Test.start("DoubleCache");

		// XXX: i was going to right this testbed, but then i got high... because got high, because got high....
		// (just kidding, it was actually my girlfriend called me and wanted to hang out)

		Test.end();
	}

}
