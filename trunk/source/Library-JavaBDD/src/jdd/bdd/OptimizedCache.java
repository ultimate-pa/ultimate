
// XXX: there is probably a bug here somewhere.
//      when partially cleaning the cache, stupid things will happen



package jdd.bdd;

import jdd.util.Configuration;
import jdd.util.JDDConsole;
import jdd.util.Test;
import jdd.util.math.Digits;


/**
 * SimpleCache + some optimization
 *
 * @see SimpleCache
 * @see Cache
 * @see DoubleCache
 */

public final class OptimizedCache extends SimpleCache {

	/**
	 * possible_bins_count is the number of possible (at most) entries in the table.
	 * if that number is zero, we wont need to clean the cache
	 */
	protected int possible_bins_count;

	/** we take note every time the cache is partially cleaned, for statistics... */
	protected int numpartial_clears;

	/** more statistics... */
	protected long partial_count, partial_kept, partial_given_up;

	/** the number of access when the last GC was done */
	private long access_last_gc;

	/** the number of garbage collection we have seen without the cache beeing used */
	private int cache_not_used_count;



	public OptimizedCache(String name, int size, int members, int bdds) {
		super(name, size, members, bdds);

		Test.check(bdds <= 3, "BDD members cannot be more than 3 for this type of cache!");

		partial_count = partial_kept= 0;
		possible_bins_count = 0;
		numpartial_clears = 0;

		access_last_gc = 0;
		cache_not_used_count = 0;
		partial_given_up = 0;
	}


	/**
	 * If this function returns true, we should wipe the cache entirely instead
	 * of a partial clean
	 */
	protected boolean shouldWipeUnusedCache() {
		// here is how it works: if the cache havent been accessed in the last
		// "Configuration.MAX_KEEP_UNUSED_PARTIAL_CACHE" garbage collection, then we
		// will wipe its contecnt since partial clean costs too much

		if(access_last_gc == numaccess) {
			cache_not_used_count++;
		} else {
			cache_not_used_count = 0;
		}

		access_last_gc = numaccess;

		return (cache_not_used_count > Configuration.MAX_KEEP_UNUSED_PARTIAL_CACHE);
	}

	// ---[ these operations just clean the cache ] ---------------------------------

	@Override
	public void invalidate_cache() {
		if(possible_bins_count != 0) {
			super.invalidate_cache();
			possible_bins_count = 0;
		}
	}


	@Override
	protected void grow_and_invalidate_cache() {
		super.grow_and_invalidate_cache();
		possible_bins_count = 0;
	}

	// ---[ these operations clean only invalid nodes ] ----------------------



	/**
	 * removes the elements that are garbage collected.
	 * this is where the "bdds" variable in constructor is used.
	 */
	@Override
	public void invalidate_cache(NodeTable nt) {

		// sanity check
		if(bdds < 1 ) {
			Test.check(false, "Cannot partiall clean a non-bdd cache!");
		}


		// if it is empty, no need to invalidate it?
		if(possible_bins_count == 0) {
			return;
		}


		// is itreally so smart to do a partial clear??
		if( shouldWipeUnusedCache() ) {
			partial_given_up++;
			invalidate_cache();
			return;
		}


		// yes, do a partial cache clear
		int ok = 0; // "ok" is the number of valid cache entries
		if(bdds == 3) {
			ok = partial_clean3(nt);
		} else if(bdds == 2) {
			ok = partial_clean2(nt);
		} else if(bdds == 1) {
			ok = partial_clean1(nt);
		}

		numpartial_clears++;
		partial_count += cache_size;	// for showStats
		partial_kept  += ok;			// for showStats
		possible_bins_count = ok;		// at this point ok = exact current bin-count
	}


	// -----------------------------------------------------------------------------
	// the partial clean stuff is divided into smaller function to help JVM
	private final int partial_clean3(NodeTable nt) {
		int ok = 0;
		for(int i = cache_size; i != 0; ) {
				i--;
			if( !isValid(i) || !nt.isValid( getIn(i,1) ) || !nt.isValid( getIn(i,2) ) || !nt.isValid( getIn(i,3) ) || !nt.isValid( getOut(i) ) ) {
				invalidate(i);
			} else {
				ok++;
			}
		}
		return ok;
	}

	private final int partial_clean2(NodeTable nt) {
		int ok = 0;
		for(int i = cache_size; i != 0; ) {
			i--;
			if( !isValid(i) || !nt.isValid( getIn(i,1) ) || !nt.isValid( getIn(i,2) ) || !nt.isValid( getOut(i) ) ) {
				invalidate(i);
			} else {
				ok++;
			}
		}
		return ok;
	}

	private final int partial_clean1(NodeTable nt) {
		int ok = 0;
		for(int i = cache_size; i != 0; ) {
			i--;
			if( !isValid(i) || !nt.isValid( getIn(i,1) ) || !nt.isValid( getOut(i) ) ) {
				invalidate(i);
			} else {
				ok++;
			}
		}
		return ok;
	}

	// -----------------------------------------------------------------------------

	@Override
	public void insert(int hash, int key1, int value) {
		super.insert(hash, key1, value);
		possible_bins_count++;
	}

	@Override
	public void insert(int hash, int key1, int key2, int value) {
		super.insert(hash, key1, key2, value);
		possible_bins_count++;
	}

	@Override
	public void insert(int hash, int key1, int key2, int key3, int value) {
		super.insert(hash, key1, key2, key3, value);
		possible_bins_count++;
	}

	// --------------------------------------------------------------
	@Override
	public int getNumberOfPartialClears() {
		return numpartial_clears;
	}

	// --------------------------------------------------------------

	@Override
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

			if(partial_given_up > 0) {
				JDDConsole.out.print("giveup=" +  partial_given_up + " ");
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
		// OptimizedCache testbench, more or less ripped from Cache.java...

		Test.start("OptimizedCache");

		// 3 elements
		OptimizedCache cache = new OptimizedCache("test", 200, 3,3);

		cache.add(2, 1,2,3);

		Test.check( cache.lookup( 2,1,2) && cache.answer == 3, "lookup 3");
		cache.add(2, 1,2,5);
		Test.check( cache.lookup( 2,1,2) && cache.answer == 5, "lookup overwritten with 5");
		Test.check( !cache.lookup( 1,1,2), "non-existing entry 1");
		Test.check( !cache.lookup( 2,2,2), "non-existing entry 2");
		Test.check( !cache.lookup( 2,2,1), "non-existing entry 3");



		// 2 elements
		cache = new OptimizedCache("test", 200, 2,2);

		cache.add(2, 1,3);
		Test.check( cache.lookup( 2,1) && cache.answer == 3, "lookup 3");
		cache.add(2, 1,5);
		Test.check( cache.lookup( 2,1) && cache.answer == 5, "lookup overwritten with 5");
		Test.check( !cache.lookup( 1,1), "non-existing entry 1");
		Test.check( !cache.lookup( 2,2), "non-existing entry 2");



		// 1 element
		cache = new OptimizedCache("test", 200, 1,1);

		cache.add(1,3);
		Test.check( cache.lookup(1) && cache.answer == 3, "lookup 3");
		cache.add(1,5);
		Test.check( cache.lookup(1) && cache.answer == 5, "lookup overwritten with 5");
		Test.check( !cache.lookup(2), "non-existing entry 1");
		Test.check( !cache.lookup(3), "non-existing entry 2");


		Test.end();

	}

}
