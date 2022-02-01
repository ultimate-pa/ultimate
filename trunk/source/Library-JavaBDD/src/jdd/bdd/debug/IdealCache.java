package jdd.bdd.debug;

import java.util.Hashtable;

import jdd.bdd.Cache;
import jdd.bdd.CacheBase;
import jdd.bdd.DoubleCache;
import jdd.bdd.NodeTable;
import jdd.bdd.OptimizedCache;
import jdd.bdd.SimpleCache;
import jdd.util.JDDConsole;
import jdd.util.math.Digits;


/**
 * An ideal cache that is have no collisions. Used for debugging only!
 *
 * It is not a part of the API and should not be accessible to users.
 *
 * @see Cache
 * @see SimpleCache
 * @see DoubleCache
 * @see OptimizedCache
 */




/* package */ public final class IdealCache extends CacheBase {

	class IdealElement {
		public int key1, key2, key3, value, hash;

		private final int good_hash(int i, int j, int k) {	return pair(i,pair(j,k));		}
		private final int pair(int i, int j) {	return ((i + j) * (i + j + 1) / 2 + i); }

		// -----------------------------------------------------------------------------

		public IdealElement(int k1, int k2, int k3, int v) {
			set(k1,k2,k3);
			value = v;
		}
		public void set(int k1, int k2, int k3) {	// lightweight support
			key1 = k1; key2 = k2; key3 = k3;
			hash = good_hash(key1, key2, key3);
		}

		@Override
		public int hashCode() { return hash; }

		@Override
		public boolean equals(Object o) {
			final IdealElement ie = (IdealElement) o;
			return key1 == ie.key1 && key2 == ie.key2 && key3 == ie.key3;
		}
	}

	// --------------------------------------------------------------------
	public int answer, hash_value;
	private final Hashtable ht;
	private final IdealElement query;	// a lightweight object
	private int numclears;
	private long numaccess;
	private long hit, miss; // cache hits and misses, hit/acces-count since last grow

	/**
	 * the arguments are:
	 * (size of elements, number of members. number of members that also are BDD nodes)
	 */
	public IdealCache(String name, int size, int members, int bdds) {
		super(name);

		ht = new Hashtable(size);
		query = new IdealElement(0,0,0,-1);


		numaccess = 0;
		hit = miss = 0;

		numclears = 0;
		hash_value = -1; // never valid
	}


	/** current size of the cache */
	public int getSize() { return ht.size(); }

	// ---[ these operations just clean the cache ] ---------------------------------

	/** just wipe the cache */
	public void invalidate_cache() {
		ht.clear();
		numclears++;
	}

	public void free_or_grow() {		invalidate_cache();	}
	public void free_or_grow(NodeTable nt) {		invalidate_cache();	}
	public void invalidate_cache(NodeTable nt) {		invalidate_cache();	}


	// -----------------------------------------------------------------------------


	public void insert(int hash, int key1, int value) {
		insert(hash, key1, -1,-1, value);
	}


	public void insert(int hash, int key1, int key2, int value) {
		insert(hash, key1, key2, -1, value);
	}



	// -----------------------------------------------------------
	public final boolean lookup(int a) {
		return lookup(a,-1,-1);
	}

	public final boolean lookup(int a, int b) {
		return lookup(a,b,-1);
	}


	public void insert(int hash, int key1, int key2, int key3, int value) {
		final IdealElement ie = new IdealElement(key1, key2, key3, value);
		ht.put(ie, ie);
	}

	public final boolean lookup(int a, int b, int c) {
		numaccess++;
		query.set(a,b,c);
		final Object obj = ht.get(query);
		if(obj == null) {
			miss++;
			return false;
		} else {
			hit++;
			final IdealElement ie = (IdealElement) obj;
			answer = ie.value;
			return true;
		}
	}

	// -----------------------------------------------------------------------------

	@Override
	public double computeLoadFactor() {
		return 100.0;
	}

	@Override
	public double computeHitRate() { // hit-rate since the last clear
		if(numaccess == 0) {
			return 0;
		}
		return ((int)((hit * 10000) / ( numaccess ))) / 100.0;
	}

	@Override
	public long getAccessCount() {		return numaccess; }
	@Override
	public int getCacheSize() { return getSize(); }
	@Override
	public int getNumberOfClears() {		return numclears;	}
	@Override
	public int getNumberOfPartialClears() {		return 0;	}
	@Override
	public int getNumberOfGrows() { return 0;			}

	public boolean check_cache(int [] crap) {
		return true; // we wouldnt find errors  even if we wanted to
	}
	// --------------------------------------------------------------

	public void showStats() {
		if(numaccess != 0) {
			JDDConsole.out.print(getName() + "-cache ");
			JDDConsole.out.print("ld=" + computeLoadFactor() + "% ");
			JDDConsole.out.print("sz="); Digits.printNumber( ht.size() );
			JDDConsole.out.print("accs="); Digits.printNumber(numaccess);
			JDDConsole.out.print("clrs=" + numclears+ "/0 ");
			JDDConsole.out.print("hitr=" + computeHitRate() + "% ");
			JDDConsole.out.println();
		}
	}


	// ----------------------------------------------------------------

	public static void main(String [] args) {
		// XXX: no test yet
	}

}
