
package jdd.zdd;


import jdd.util.*;
import jdd.bdd.*;
import jdd.bdd.debug.*;

import java.util.*;


/**
 * Base implementation for Zero-Supressed Binary Decision Diagrams (Z-BDDs).
 * Z-BDDs are a special type of BDDs that are more suited for sparse sets.
 * For example, if you are working with a set that is most of the time empty,
 * you might want to use Z-BDDs instead of BDDs.
 * <p>
 * The base implementation will give you the core Z-BDD operation such as
 * change, diff and union. To get more operators, see the sub-classes.
 *
 * @see BDD
 * @see ZDD2
 * @see ZDDCSP
 */

// NOTE FOR DEVELOPERS:
// Zero-suppressed BDDs use INVERSE variable order: v_last at top, v_0 at
//      bottom just above 0 and 1.
//
//	  To make implementaion easier,
//	  v_0 has t_var of 0 while 0 and 1 are assigned t_var of -1.


public class ZDD  extends NodeTable  {
	private static final int CACHE_SUBSET0 = 0, CACHE_SUBSET1 = 1, CACHE_CHANGE = 2,
							CACHE_UNION = 3, CACHE_INTERSECT = 4, CACHE_DIFF = 5;

	protected int num_vars; /** number of Z-BDD variables */
	private int node_count_int; /** internal variable used by nodeCount */
	private OptimizedCache unary_cache;		// for unary stuff. (ZDD, variable, op) => ZDD
	private OptimizedCache binary_cache;	// for binary operations. (ZDD, ZDD, op) => ZDD
	protected NodeName nodeNames = new ZDDNames();

	/**
	 * create a Z-BDD manager
	 * @param nodesize is the number of nodes initially allocated in the node-table
	 */
	public ZDD(int nodesize) {
		this(nodesize, Configuration.DEFAULT_ZDD_CACHE_SIZE);
	}

	/**
	 * create a Z-BDD manager
	 * @param nodesize is the number of nodes initially allocated in the node-table
	 * @param cachesize is the suggested cache size.
	 */

	public ZDD(int nodesize, int cachesize) {
		super(nodesize);


		unary_cache = new OptimizedCache("unary", cachesize / Configuration.zddUnaryCacheDiv, 3, 1);
		binary_cache = new OptimizedCache("binary", cachesize / Configuration.zddBinaryCacheDiv, 3, 2);


		// FIXME:
		// we can do this, but it wont include the base-class (ZDD2, ZDDCSP etc) caches:
		if(Options.profile_cache)  new jdd.bdd.debug.BDDDebugFrame(this);

		// yes, we know how deep our trees are and will call tree_depth_changed()!
		enableStackMarking();
	}


	// ---------------------------------------------------------------
	/** cleanup this ZDD, to release its memory and help GC */
	public void cleanup() {
		super.cleanup();
		binary_cache = null;
		unary_cache = null;
	}
	// ---------------------------------------------------------------
	// Debugging stuff
	public Collection addDebugger(BDDDebuger d) {
		Collection v = super.addDebugger( d );
		v.add( unary_cache );
		v.add( binary_cache );
		return v;
	}
	// ---------------------------------------------------------------

	protected void post_removal_callbak() {
		binary_cache.free_or_grow(this);
		unary_cache.free_or_grow(this);
	}

	/** Zero-supressed MK operator */
	protected final int mk(int i, int l, int h) {
		if(h == 0) return l; /* ZDD node elimination */
		return add(i,l,h);
	}



	// -------------------------------------------
    /** create a new ZDD variable */
	public int createVar() {
		int ret = num_vars++;
		// we want to keep the work stack at least so large
		int need = 5 * num_vars + 3;
		if(work_stack.length < need)
			work_stack = Array.resize(work_stack, work_stack_tos, need);

		tree_depth_changed(num_vars); // MUST be called
		return ret;
	}
	// --------------------------------------------------------
    
    /** returns {} */
	public final int empty() { return 0; }
    
    /** returns {{}} */
	public final int base() { return 1; }
    
    /** create a tree of a variable. single(vx) = { vx } */
	public final int single(int var) { return mk(var, 0, 1); }

	public final int universe() {
		int last = 1;
		for(int i = 0; i < num_vars; i++) {
			work_stack[work_stack_tos++] = last;
			last = mk(i, last, last);
			work_stack_tos--;
		}
		return last;
	}
    
    /** cube of a single variable v */
	public final int cube(int v) { return mk(v, 0, 1) ; }
    
    /** cube of a selection of variables */
	public final int cube(boolean [] v) {
		int last = 1;
		for(int i = 0; i < v.length; i++)
			if( v[i] ) {
				work_stack[work_stack_tos++] = last;
				last = mk(i, 0, last);
				work_stack_tos--;
			}
		return last;
	}
    
    /**
     * cube of a selection of variables, represented as
     * a string, e.g. "11001"
     */
	public final int cube(String s) {
		int len = s.length();
		int last = 1;
		for(int i = 0; i < len; i++)
			if( s.charAt(len - i - 1) == '1') {
				work_stack[work_stack_tos++] = last;
				last = mk(i, 0, last);
				work_stack_tos--;
			}
		return last;
	}
    /**
     * Union of cubes, each represented by a string token.
     * 
     * This function was added to ease fast creation of
     * sets of sets in tests.
     * 
     * E.g. "0001 1000 1101" => { v1, v4, v4v3v1 }
     */
    public int cubes_union(String s) {
        return do_cubes_op(s, true);
    }
    
    /**
     * Intersection of cubes. same as
     * cubes_unon() but uses intersect instead of union
     */
    public int cubes_intersect(String s) {
        return do_cubes_op(s, false);
    }
    
    private int do_cubes_op(String s, boolean do_union) {
        StringTokenizer st = new StringTokenizer(s," \t\n,;");
        int ret = -1;
        
        while(st.hasMoreTokens()) {
            String str = st.nextToken();            
            int c = cube(str);
            
            if(ret == -1) ret = c;
            else {
                ref(ret);
                ref(c);
                int tmp1 = do_union ? union(ret,c) : intersect(ret,c);
                deref(ret);
                deref(c);
                ret = tmp1;
            }
        }
        return ret;
    }
    
	public int subsets(boolean [] v) {
		int last = 1;
		for(int i = 0; i < v.length; i++)
			if( v[i] ) {
				work_stack[work_stack_tos++] = last;
				last = mk(i, last, last);
				work_stack_tos--;
			}
		return last;
	}

	//-----------------------------------------------
	/** var is a variable, NOT a tree */
	public final int subset1(int zdd, int var) {
		if(var < 0 || var >= num_vars) return -1; // INVALID VARIABLE!

		if(getVar(zdd) < var) return 0;
		if(getVar(zdd) == var) return getHigh(zdd);

		// ... else if(getVar(zdd) > var)

		if(unary_cache.lookup(zdd, var, CACHE_SUBSET1)) return unary_cache.answer;
		int hash = unary_cache.hash_value;

		int l = work_stack[work_stack_tos++] = subset1( getLow(zdd), var);
		int h = work_stack[work_stack_tos++] = subset1( getHigh(zdd), var);
		l = mk( getVar(zdd), l, h);
		work_stack_tos -= 2;

		unary_cache.insert(hash, zdd, var, CACHE_SUBSET1, l);
		return l;
	}

	/** var is a variable, NOT a tree */
	public final int subset0(int zdd, int var) {
		if(var < 0 || var >= num_vars) return -1; // INVALID VARIABLE!

		if(getVar(zdd) < var) return zdd;
		if(getVar(zdd) == var) return getLow(zdd);

		// ... else if(getVar(zdd) > var)
		if(unary_cache.lookup(zdd, var, CACHE_SUBSET0)) return unary_cache.answer;
		int hash = unary_cache.hash_value;

		int l = work_stack[work_stack_tos++] = subset0( getLow(zdd), var);
		int h = work_stack[work_stack_tos++] = subset0( getHigh(zdd), var);
		l = mk( getVar(zdd), l, h);
		work_stack_tos -= 2;
		unary_cache.insert(hash, zdd, var, CACHE_SUBSET0, l);
		return l;
	}

	public final int change(int zdd, int var) {
		if(var < 0 || var >= num_vars) return -1; // INVALID VARIABLE!


		if(getVar(zdd) < var) return mk(var, 0, zdd);
		// XXX: ARASH FIX THIS TRUELY STUPID BUG: if(getVar(zdd) == var) return mk(var, getVar(zdd), getVar(zdd));
		if(getVar(zdd) == var) return mk(var, getHigh(zdd), getLow(zdd));

		// else if(v > var)
		if(unary_cache.lookup(zdd, var, CACHE_CHANGE)) return unary_cache.answer;
		int hash = unary_cache.hash_value;


		int l = work_stack[work_stack_tos++] = change( getLow(zdd), var);
		int h = work_stack[work_stack_tos++] = change( getHigh(zdd), var);
		l = mk( getVar(zdd), l, h);
		work_stack_tos -= 2;

		unary_cache.insert(hash, zdd, var, CACHE_CHANGE, l);
		return l;
	}


	public final int union(int p, int q) {
		if(getVar(p) > getVar(q)) return union(q,p);
		if(p == 0) return q;
		if(q == 0 || q == p) return p;
		// NOT USEFULL HERE: if(p == 1) 	return insert_base(q);


		if(binary_cache.lookup(p, q, CACHE_UNION)) return binary_cache.answer;
		int hash = binary_cache.hash_value;

		int l;
		if(getVar(p) < getVar(q)) {
			l = work_stack[work_stack_tos++] = union(p, getLow(q));
			l = mk(getVar(q), l, getHigh(q));
			work_stack_tos--;
		} else {
			l = work_stack[work_stack_tos++] = union( getLow(p), getLow(q));
			int h = work_stack[work_stack_tos++] = union(getHigh(p), getHigh(q));
			l = mk( getVar(p), l, h);
			work_stack_tos -= 2;
		}

		binary_cache.insert(hash, p, q, CACHE_UNION, l);
		return l;
	}


	public final int intersect(int p, int q) {
		if(p == 0 || q == 0) return 0;
		if(q == p) return p;
		if(p == 1) return follow_low(q);	// ADDED BY ARASH, NOT TESTED VERY MUCH YET, DONT NOW IF IT MAKES THINGS FASTER OR SLOWER!!
		if(q == 1) return follow_low(p);	//  (not in the original Minato paper)



		if(binary_cache.lookup(p, q, CACHE_INTERSECT)) return binary_cache.answer;
		int hash = binary_cache.hash_value;

		int l = 0;
		if(getVar(p) > getVar(q)) l =  intersect( getLow(p), q);
		else if(getVar(p) < getVar(q)) l =  intersect( p, getLow(q));
		else {
		// else if getVar(p) == getVar(q)
			l = work_stack[work_stack_tos++] = intersect( getLow(p), getLow(q));
			int h = work_stack[work_stack_tos++] = intersect(getHigh(p), getHigh(q));
			l = mk( getVar(p), l, h);
			work_stack_tos -= 2;
		}

		binary_cache.insert(hash, p, q, CACHE_INTERSECT, l);
		return l;
	}

	public final int diff(int p, int q) {
		if(p == 0 || p == q ) return 0;
		if(q == 0) return p;

		if(binary_cache.lookup(p, q, CACHE_DIFF)) return binary_cache.answer;
		int hash = binary_cache.hash_value;

		int l = 0;
		if(getVar(p) < getVar(q)) l =  diff( p, getLow(q));
		else if(getVar(p) > getVar(q)) {
			l = work_stack[work_stack_tos++] = diff( getLow(p), q);
			l = mk( getVar(p), l, getHigh(p));
			work_stack_tos--;
		} else { // getVar(p) == getVar(q);
			l = work_stack[work_stack_tos++] = diff( getLow(p), getLow(q));
			int h = work_stack[work_stack_tos++] = diff(getHigh(p), getHigh(q));
			l = mk( getVar(p), l, h);
			work_stack_tos -= 2;
		}

		binary_cache.insert(hash, p, q, CACHE_DIFF, l);
		return l;
	}


	// ----[ misc, mostly early-termination stuff ]------------------------------------

	/** returns the terminal value along the all-low path */
	public final int follow_low(int zdd) {
		while( zdd >= 2) zdd = getLow(zdd);
		return zdd;
	}

	/** returns the terminal value along the all-high path */
	public final int follow_high(int zdd) {
		while( zdd >= 2) zdd = getHigh(zdd);
		return zdd;
	}
	/** returns true if base {{}} is in X */
	public final boolean emptyIn(int X) {
		return (follow_low(X) == 1);
	}

	/** computes set U {base} */
	private final int insert_base(int set) {
		if(set < 2) return 1; // <-- the magic happens here
		int l = work_stack[work_stack_tos++] = insert_base(getLow(set));
		l = (getLow(set) == l) ? set : mk(getVar(set), l, getHigh(set));
		work_stack_tos--;
		return l;
	}

	// --- [ satOne ] ----------------------------------------------
	/** Returns a satisfying boolean assignment, null if none<br>XXX: this code is still untested! */
	public boolean [] satOne(int zdd, boolean [] vec) {
		if(zdd == 0) return null;
		if(vec == null) vec = new boolean[num_vars];
		Array.set(vec, false);
		if(zdd != 1) satOne_rec(zdd, vec);
		return vec;
	}
	private void satOne_rec(int zdd, boolean [] vec) {
		if(zdd < 2) return;
		int next = getLow(zdd);
		if(next == 0 ){
			vec[ getVar(zdd) ] = true;
			next = getHigh(zdd);
		}
		satOne_rec(next, vec);
	}
	// --- [ misc] ----------------------------------------------
	public final int count(int zdd) {
		if(zdd < 2) return zdd;
		return count(getLow(zdd)) +  count(getHigh(zdd));
	}

	// ----[ node count ] ----------------------------
	/** compute the number of nodes in the tree (this function is currently somewhat slow)*/
	public int nodeCount(int zdd) {
		node_count_int = 0;
		nodeCount_mark(zdd);
		unmark_tree(zdd);
		return node_count_int;
	}

	/** recursively mark and count nodes, used by nodeCount*/
	private final void nodeCount_mark(int zdd) {
		if(zdd < 2) return;

		if( isNodeMarked(zdd)) return;
		mark_node(zdd);
		node_count_int++;
		nodeCount_mark( getLow(zdd) );
		nodeCount_mark( getHigh(zdd) );
	}

	// --- [ helper stuff ]---------------------------------------------
	/** helper function to compute set' = set UNION add, derefs the old set! */
	public int unionTo(int set, int add) {
		int tmp = ref( union(set, add) );
		deref(set);
		return tmp;
	}
	/** helper function to compute set' = set - add, derefs the old set! */
	public int diffTo(int set, int add) {
		int tmp = ref( diff(set, add) );
		deref(set);
		return tmp;
}
	// --- [ debug ] ----------------------------------------------
	/** show ZDD statistics */
	public void showStats() {
		super.showStats();
		unary_cache.showStats();
		binary_cache.showStats();
	}

	/** return the amount of internally allocated memory in bytes */
	public long getMemoryUsage() {
		long ret = super.getMemoryUsage();
		if(unary_cache != null) ret += unary_cache.getMemoryUsage();
		if(binary_cache != null) ret += binary_cache.getMemoryUsage();
		return ret;
	}

	public void setNodeNames(NodeName nn) {
		nodeNames = nn;
	}

	public void print(int zdd) { ZDDPrinter.print(zdd, this, nodeNames);	}
	public void printDot(String fil, int bdd) {	ZDDPrinter.printDot(fil, bdd, this, nodeNames);	}
	public void printSet(int bdd) {	ZDDPrinter.printSet(bdd,  this, nodeNames);	}
	public void printCubes(int bdd) {	ZDDPrinter.printSet(bdd, this, null);	}
	// -------------------------------------------------

	/** testbench. do not call */
	public static void internal_test() {

		Test.start("ZDD");

		ZDD zdd = new ZDD(100);


		// test some basic stuffs first:
		Test.checkEquality( zdd.getVar(0) , -1, "false.top");
		Test.checkEquality( zdd.getVar(1) , -1, "true.top");

		int x1 = zdd.createVar();
		int x2 = zdd.createVar();

		int a = zdd.empty();
		int b = zdd.base();
		int c = zdd.change(b, x1);
		int d = zdd.change(b, x2);
		int e = zdd.union(c,d);
		int f = zdd.union(b,e);
		int g = zdd.diff(f,c);


		// directly from minatos paper, figure 9
		// [until we find a better way to test isomorphism...]
		Test.checkEquality( a, 0, "emptyset = 0");
		Test.checkEquality( b, 1, "base = 1");
		Test.checkEquality( c, zdd.mk(x1,0,1) , "C");
		Test.checkEquality( d, zdd.mk(x2,0,1) , "D");
		Test.checkEquality(zdd.getLow(e), c, "E");
		Test.checkEquality(zdd.getHigh(e), 1, "E");
		int tmp = zdd.mk(x1, 1,1);
		Test.checkEquality(zdd.getLow(f), tmp, "F");
		Test.checkEquality(zdd.getHigh(f), 1, "F");
		Test.checkEquality(g, zdd.mk(x2, 1,1) , "G");


		// intersect
		Test.checkEquality( zdd.intersect(a, b), a, "intersect (1)");
		Test.checkEquality( zdd.intersect(a, a), a, "intersect (2)");
		Test.checkEquality( zdd.intersect(b, b), b, "intersect (3)");
		Test.checkEquality( zdd.intersect(c, e), c, "intersect (4)");
		Test.checkEquality( zdd.intersect(e, f), e, "intersect (5)");
		Test.checkEquality( zdd.intersect(e, g), d, "intersect (6)");

		// union
		Test.checkEquality( zdd.union(a, a), a, "union (1)");
		Test.checkEquality( zdd.union(b, b), b, "union (2)");
		Test.checkEquality( zdd.union(a, b), b, "union (3)");
		Test.checkEquality( zdd.union(g, e), f, "union (4)");

		// diff:
		Test.checkEquality( zdd.diff(a,a), a, "diff (1)");
		Test.checkEquality( zdd.diff(b,b), a, "diff (2)");
		Test.checkEquality( zdd.diff(d,c), d, "diff (3)");
		Test.checkEquality( zdd.diff(c,d), c, "diff (4)");
		Test.checkEquality( zdd.diff(e,c), d, "diff (5)");
		Test.checkEquality( zdd.diff(e,d), c, "diff (6)");
		Test.checkEquality( zdd.diff(g,b), d, "diff (7)");

		Test.checkEquality( zdd.diff(g,d), b, "diff (8)");
		Test.checkEquality( zdd.diff(f,g), c, "diff (9)");
		Test.checkEquality( zdd.diff(f,e), b, "diff (10)");


		// subset0
		Test.checkEquality( zdd.subset0(b, x1), b , "subset0 (1)");
		Test.checkEquality( zdd.subset0(b, x2), b , "subset0 (2)");
		Test.checkEquality( zdd.subset0(d, x2), a , "subset0 (3)");
		Test.checkEquality( zdd.subset0(e, x2), c , "subset0 (4)");

		// subset1
		Test.checkEquality( zdd.subset1(b, x1), 0 , "subset1 (1)");
		Test.checkEquality( zdd.subset1(b, x2), 0 , "subset1 (2)");
		Test.checkEquality( zdd.subset1(d, x2), b , "subset1 (3)");
		Test.checkEquality( zdd.subset1(g, x2), b , "subset1 (4)");
		Test.checkEquality( zdd.subset1(g, x1), a , "subset1 (5)");
		Test.checkEquality( zdd.subset1(e, x2), b , "subset0 (6)");



		// this is the exact construction sequence of Fig.14 in "Zero-suppressed BDDs and their application" by Minato
		int x3 = zdd.createVar();
		int x4 = zdd.createVar(); // not used
		tmp = zdd.union(1, zdd.change(1, x1));
		int tmp2 = zdd.change(tmp, x2);
		tmp = zdd.union(tmp, tmp2);
		int fig14 = zdd.union(tmp, zdd.change(1, x3));


		// this is the exact construction sequence of Fig.13 in "Zero-suppressed BDDs and their application" by Minato
		boolean [] minterm = new boolean[4];
		minterm[3] = minterm[2] = minterm[1] = true; minterm[0] = false;
		tmp = zdd.subsets(minterm);
		minterm[0] = true; minterm[1] = false;
		tmp2 = zdd.subsets(minterm);
		tmp = zdd.intersect(tmp,tmp2);

		minterm[3] = minterm[0] = minterm[1] = true; minterm[2] = false;
		tmp2 = zdd.subsets(minterm);
		tmp = zdd.union(tmp2, tmp);
		minterm[2] = minterm[3] = minterm[0] = true; minterm[3] = false;
		tmp2 = zdd.subsets(minterm);
		int fig13 = zdd.intersect(tmp2, tmp);

		Test.checkEquality(fig13, fig14, "Fig.13 and Fig.14 yield equal result");


		// some other tests from minatos paper "ZBDDs and their applications..."
		// 1. INTERSECT
		tmp  = zdd.cubes_union("100 011 010");
        tmp2 = zdd.union( zdd.cube("11"), 1);
        int tmp3 = zdd.intersect(tmp, tmp2);
		int answer = zdd.cube("11");
		Test.checkEquality(tmp3, answer, "intersect test");
		Test.checkEquality(zdd.work_stack_tos, 0, "TOS restored after intersect");

		// 2. UNION
		tmp3 = zdd.union(tmp, tmp2);
		answer = zdd.union(tmp, 1);
		Test.checkEquality(tmp3, answer, "union test");
		Test.checkEquality(zdd.work_stack_tos, 0, "TOS restored after union");

		// 3. DIFF
		tmp3 = zdd.diff(tmp, tmp2);
		answer = zdd.union( zdd.cube("10"), zdd.cube("100") );
		Test.checkEquality(tmp3, answer, "diff test");
		Test.checkEquality(zdd.work_stack_tos, 0, "TOS restored after diff");



		Test.end();
	}
}
