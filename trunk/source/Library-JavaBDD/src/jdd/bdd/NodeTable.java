package jdd.bdd;


import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import jdd.bdd.debug.BDDDebuger;
import jdd.util.Allocator;
import jdd.util.Array;
import jdd.util.Configuration;
import jdd.util.JDDConsole;
import jdd.util.Options;
import jdd.util.Test;
import jdd.util.math.HashFunctions;

/**
 * implementation of a node table of elements (var,low,high,ref-count) that supports garbage collections.
 *
 */

// the nodes are unique, which is guranteed by a double linked list hash-table-alike structure.
// this structure is very similiar to the double-hashed list in BuDDy.
//
// we divide the node list and the linked-list into to parts (t_nodes, t_list).
// this gives a bad cache performance (CPU cache, not BDD operation caches),
// but it might help to keep the memory peek down a little bit.


public class NodeTable {

	/** used to mark/unmark BDD nodes */
	public static final int NODE_MARK = 0x80000000, NODE_UNMARK = 0x7FFFFFFF;

	private static final short MAX_REFCOUNT = 32767; /** the largest possible ref-count */

	// monolithic nodetable stuff
	private static final int NODE_WIDTH = 3; // how many ints a node occupy
	private static final int OFFSET_VAR = 1; // offset of the var member
	private static final int OFFSET_LOW = 0; // offset of the low member
	private static final int OFFSET_HIGH = 2; // offset of the high member

	// monolithic double linked-list stuff
	private static final int LIST_WIDTH = 2; // how many ints a linked list occupy
	private static final int OFFSET_NEXT = 0; // offset of the next pointer
	private static final int OFFSET_PREV = 1; // offset of the prev pointer


	/** the "debuggers" connected to this NodeTable. see for example ProfibedBDD2 */
	private final Collection debugers;

	protected int table_size, stat_nt_grow, dead_nodes;
	protected int nodesminfree /* , bddmaxnodeincrease, minfreenodes */ ;
	private int [] t_nodes;	 /** for monolithic nodetable */
	private int [] t_list;	 /** for the linked list */
	private short [] t_ref; /** the reference counter */
	private int first_free_node, free_nodes_count;
	private boolean stack_marking_enabled; /** if true, we will use the faster version of mark_tree() */


	// GC/grow stuff
	protected int stat_gc_count, stat_lookup_count;
	protected long stat_gc_freed, stat_gc_time, stat_grow_time, stat_notify_time;
	protected int [] work_stack, mark_stack;
	protected int work_stack_tos;
	protected long ht_chain;



	public NodeTable(int nodesize) {
		debugers = new LinkedList();

		// we dont like nodetables that are too small
		if(nodesize < Configuration.MIN_NODETABLE_SIZE) {
			nodesize = Configuration.MIN_NODETABLE_SIZE;
		}

		// allocate the initial arraus
		table_size = nodesize;
		t_ref = Allocator.allocateShortArray(table_size);
		t_nodes = Allocator.allocateIntArray(table_size * NODE_WIDTH);
		t_list = Allocator.allocateIntArray(table_size * LIST_WIDTH);


		first_free_node = 2;
		free_nodes_count = nodesize -2;
		for(int i = 0; i < nodesize; i++) {
			invalidate(i);
			setPrev(i, 0);
			setNext(i, i+1);
		}

		setNext(nodesize-1, 0);

		// get 1 and zero:
		setAll(0, -1, 0, 0, MAX_REFCOUNT);
		setAll(1, -1, 1, 1, MAX_REFCOUNT);


		update_grow_parameters();
		stat_nt_grow = 0; // number of times we expand the table
		dead_nodes = 0; // no dead nodes yet


		// hash table stuff
		stat_gc_count = stat_lookup_count = 0;
		stat_gc_freed = stat_gc_time = stat_grow_time = stat_notify_time = 0L;
		ht_chain = 0;

		work_stack = Allocator.allocateIntArray(32); // just some silly number
		mark_stack = Allocator.allocateIntArray( work_stack.length );
		work_stack_tos = 0;

		stack_marking_enabled = false; // disable by default
	}

	// --------------------------------------------------------------------
	public void cleanup() { // to help GC
		stopDebuggers();
		t_ref = null;
		t_nodes = null;
		t_list = null;
		work_stack = null;
		mark_stack = null;
	}

	/**
	 * this function MUST be called when a paramater that may change the tree dpeth
	 *  (such as the number of variables in a BDD) has changed!
	 */
	protected void tree_depth_changed(int n) {
		// mark_stack is the stack used for recursive tree marking
		final int need = n * 4 + 3;
		if(mark_stack.length < need)
		 {
			mark_stack = Allocator.allocateIntArray(need * 2); // twice, so we dont need to do it too often....
		}
	}
	// --- [ HT stuff ] ----------------------------------------------------------------
	// compute hash for the triple (i,l,h)
	// this function can change very much between the releases :)
	private final int compute_hash(int i, int l, int h) {
		return (HashFunctions.hash_prime(i,l,h) & 0x7FFFFFFF) %  table_size;
	}



	/**
	 * how much can we allow this node-table to increase??
	 *
	 * <p>TODO: we should also check how much free memory we have!
	 */
	private final int compute_increase_limit(int current_size) {
		// limit disabled?
		if(Configuration.nodetableSmallSize <= 0 || Configuration.nodetableLargeSize <= 0) {
			return current_size;
		}

		if(current_size <= Configuration.nodetableSmallSize) {
			return Configuration.nodetableGrowMax;
		}
		if(current_size >= Configuration.nodetableLargeSize) {
			return Configuration.nodetableGrowMin;
		}


		// avoid division by zero, when badly configured
		if(Configuration.nodetableLargeSize == Configuration.nodetableSmallSize) {
			return (Configuration.nodetableGrowMax + Configuration.nodetableGrowMin) / 2;
		}

		// anywhere between the two limits, we use a linear interpolation of them.
		return Configuration.nodetableGrowMax -
			( (current_size - Configuration.nodetableSmallSize) *
				(Configuration.nodetableGrowMax - Configuration.nodetableGrowMin)) /
				(Configuration.nodetableLargeSize - Configuration.nodetableSmallSize);
	}

	/**
	 * this function is called when something in the node table is changed (GC or grow).
	 *
	 * <p> sub-classes must "implement" this function for, for example, flushing caches
	 * since it signals that something important has been changed and old data might have
	 * become invalid.
	 */
	protected void post_removal_callbak() { /* do nothing */ }

	protected final void signal_removed() {
		final long time = System.currentTimeMillis();
		post_removal_callbak();
		stat_notify_time += System.currentTimeMillis() - time;

	}
	/**
	 * do a garbage collection.
	 * @return number of freed nodes
	 */
	public int gc() { return gc(true); }

	/**
	 * this is the internal version of gc(). when called from NodeTable internally,
	 * we might to choose to call signal_removed() not here but at a later point.
	 */
	private int gc(boolean call_callback) {
		final long time = System.currentTimeMillis();
		stat_gc_count ++;


		// 0. mark nodes in use
		mark_nodes_in_use();

		// 1. free or re-hash and unmark
		final int old_free = free_nodes_count;
		first_free_node = free_nodes_count = 0;

		// 1.5 go backward to get the list in correct direction. doesnt really matter :(
		for(int i = table_size; i > 2; ) {
			i--;
			if(isValid(i) && isNodeMarked(i)) {
				unmark_node(i);
				final int pos = compute_hash( getVar(i), getLow(i), getHigh(i));
				connect_list(i, pos);
			} else {
				invalidate(i);
				setNext(i, first_free_node);
				first_free_node = i;
				free_nodes_count ++;
			}
		}

		// 2. ok, we have removed things, inform others [caches ?] about it
		if(call_callback) {
			signal_removed();
		}

		// 3. update our statistics
		stat_gc_time += System.currentTimeMillis() - time;
		final int new_free = free_nodes_count - old_free;
		stat_gc_freed  += new_free ;

		if(Options.verbose) {
			JDDConsole.out.println("Garbage collection #" + stat_gc_count + ": " + table_size + " nodes, " + new_free + " freed, time " + stat_gc_time +"+"+ stat_notify_time );
		}

		return new_free;
	}

	/**
	 * this functions marks the nodes in use AND cleans the <tt>prev</tt> link.
	 * we had a version that used t_list as stack and avoided recursive calls
	 * with mark_tree. there are some problems with that but we might switch back to it for better efficiency
	 */
	private final void mark_nodes_in_use() {
		// insert the stuff we are working on:
		for(int i = 0; i < work_stack_tos; i++) {
			mark_tree(work_stack[i]);
		}

		// and referenced nodes.
		// it looks inefficient, but you cant do it much faster than this :(
		for(int i = table_size; i != 0; ) {
			i--;
			if( isValid(i)  && getRefPlain(i) > 0) {
				mark_tree(i);
			}
			setPrev(i, 0);
		}
	}

	/**
	 * grow is called when we need more nodes in the table. it first will try to
	 * make more room by a garbage collection. if that fails, the node table is resized
	 */
	protected void grow() {

		// if we have no dead nodes, we dont bother to collect garbage,
		// but the dead-node counter is bot always accurate
		if(dead_nodes > 0 || table_size > Configuration.nodetableSimpleDeadcountThreshold) {

			final int got = gc(false);
			dead_nodes = 0;

			// we might have had DEAD NODES, but that doesnt mean that we can always
			// free those nodes (they can be used in some other tree)
			// furthermore, we must of at least minfreenodes% free nodes or we will grow
			if(got >= nodesminfree ){
				signal_removed(); // Force all caches to be wiped out!
				return;
			}
		}

		// could  not GC, start growing:
		long time = System.currentTimeMillis();

		// 1. grow node table:
		stat_nt_grow++;

		// 1.b) compute the new size.
		// this snippet is not very intelligent. I just don't feel like re-writing it right now
		// int new_size = table_size + Math.min(table_size, compute_increase_limit(table_size) );
		final int new_size = table_size + compute_increase_limit(nodesminfree) ;



		// 2. resize tables
		final int old_size = table_size;
		resize(new_size);
		table_size = new_size;



		// 3. update the new array to become a unique node table
		/*
		// this is what we had before (kinda inefficient ha?)
		for(int i = old_size; i < new_size; i++)  invalidate(i);
		clearPrev(0, new_size);
		recompute_hash();
		*/


		// 3.a) start clean
		first_free_node =  free_nodes_count = 0;

		// 3.b) invalidate the new nodes and insert them into the linked list
		for(int i = new_size; i > old_size; )  {
			i--;
			invalidate(i);
			setPrev(i, 0);
			setNext(i, first_free_node);
			first_free_node = i;
			free_nodes_count++;
		}

		// 3.c) clear the rest.
		clearPrev(0, old_size); // XXX: how do we embed this in the loop below??

		// 3.d) now seperate the old and new invalid nodes
		for(int i = old_size; i > 2; ) {
			i--;
			if(isValid(i)) {
				final int hash = compute_hash( getVar(i), getLow(i), getHigh(i));
				connect_list(i, hash);
			} else {
				setNext(i, first_free_node);
				first_free_node = i;
				free_nodes_count++;
			}
		}


		//4. update internal variables that need to be upated...
		update_grow_parameters();

		// 5. force all caches to be wiped out!
		signal_removed();

		// 6. and statictics...
		time = System.currentTimeMillis() - time;
		stat_grow_time += time;

		if(Options.verbose) {
			JDDConsole.out.println("Node-table grown #" + stat_nt_grow + ": " + old_size + " -> " + new_size  + " nodes, time " + stat_grow_time);
		}
	}

	public int add(int v, int l, int h) {

		int hash = compute_hash(v,l,h);
		int curr = getPrev(hash);

		// look it up in the cache
		stat_lookup_count++;
		while(curr != 0) {
			if( match_table(curr, v,l,h))
			 {
				return curr; // tuple found in the table!
			}
			curr = getNext(curr);
			ht_chain++;

		}


		// see if we have room for it!
		if(free_nodes_count < 2 ) { // dont change "2" to "0" !
			grow();
			hash = compute_hash(v,l,h); // table_size might have changed (or not if we only did a GC)
		}

		// takke next free node
		curr = first_free_node;
		first_free_node = getNext(first_free_node);
		free_nodes_count--;

		// adjust and write node
		setAll(curr, v,l,h, (short)-1);

		connect_list(curr, hash);
		return curr;
	}

	// --------------------------------------------------------------------

	/**
	 * for debugging: install a debugger. returns the set of caches.
	 */
	public Collection addDebugger(BDDDebuger d) {
		debugers.add(d);
		final Collection v = new LinkedList();

		// at this level, we wont do anything with the returned vector.
		// the sub-classes will do that.

		return v;
	}

	/**
	 * stop the running debuggers, otherwise they will keep collecting data.
	 * called from cleanup()
	 */
	private void stopDebuggers() {
		for (final Iterator e = debugers.iterator() ; e.hasNext() ;) {
			final BDDDebuger d = (BDDDebuger) e.next();
			d.stop();
		}
	}

	// ---------------------------------------------------------------

	/**
	 * this is called when the table ha grown and we might need to
	 * update some internal parameters
	 */
	protected void update_grow_parameters() {
		nodesminfree = Math.min( (table_size * Configuration.minFreeNodesProcent) / 100, Configuration.maxNodeFree -1);
	}

	// ---- [resizeing algo] ---------------------------------------------------

	/** resize the tables */
	private void resize(int new_size) {

		t_ref = Array.resize(t_ref, table_size, new_size);
		try {
			t_nodes = Array.resize(t_nodes, NODE_WIDTH * table_size, NODE_WIDTH * new_size);
			t_list = Array.resize(t_list, LIST_WIDTH * table_size, LIST_WIDTH * new_size);
		} catch(final OutOfMemoryError ignored) {
			if(Options.verbose) {
				JDDConsole.out.println("NodeTable.resize failed...");
			}
                    System.exit(20);
		}
	}

	// -------- [ refocunting ] ---------------------------------------------------
	/**
	 * increase the reference-count of this BDD once
	 * @return bdd
	 */
	public final int ref(int bdd) {
		short ref = getRefPlain(bdd);
		if(ref == -1) {
			ref = 1;
		} else if(ref == 0) {
			ref = 1;
			dead_nodes --;
		} else if(ref != MAX_REFCOUNT) {
			ref++;
		}
		setRef(bdd, ref);
		return bdd;
	}
	/**
	 * decrease the reference-count of this BDD once.
	 * @return bdd
	 */
	public final int deref(int bdd) {
		short ref = getRefPlain(bdd);
		if(ref == 1) {
			ref = (short) 0;
			dead_nodes++;
		} else if(ref!= MAX_REFCOUNT && ref > 0) {
			ref--;
		}
		setRef(bdd, ref);
		return bdd;

	}

	/**
	 * set the reference-count of this BDD to max.
	 * after that, the ref-count cant be changed and the node cannot be garbage collected anymore.
	 * <p>DO NOT USE, unless you know what you are doing (note: you probably don't).
	 */
	public final void saturate(int bdd) {
		setRef(bdd, MAX_REFCOUNT);
	}


	// ------- [ low-level access ] --------------------------------------------------------------


	// low-level access to the ref-counter
	private final short getRefPlain(int bdd) { return t_ref[bdd]; }	/** just return the number */
	private final void setRef(final int bdd, final short r) {		t_ref[bdd] = r;	}

	/**
	 * get the number of references to this BDD.
	 */
	public final short getRef(int bdd) {
		if(t_ref[bdd] == -1) {
			return 0;
		}
		return t_ref[bdd];
	}




	// -----------------------------------------------------------------------------------------
	// low-level access to the node table
	private final void setVar(final int bdd, int v) { t_nodes[OFFSET_VAR + NODE_WIDTH * bdd] = v; }
	private final void setLow(int bdd, int v) { t_nodes[OFFSET_LOW + NODE_WIDTH * bdd] = v; }
	private final void setHigh(int bdd, int v) { t_nodes[OFFSET_HIGH + NODE_WIDTH * bdd] = v; }

	public final int getVar(final int bdd) {	return t_nodes[OFFSET_VAR + NODE_WIDTH * bdd];	}
	public final int getLow(final int bdd) {	return t_nodes[OFFSET_LOW + NODE_WIDTH * bdd];	}
	public final int getHigh(final int bdd) {	return t_nodes[OFFSET_HIGH + NODE_WIDTH * bdd];	}

	/** return the associated variable. works even when the table is marked */
	protected  final int getVarUnmasked(int bdd) {	return t_nodes[OFFSET_VAR + NODE_WIDTH * bdd] & NODE_UNMARK; }

	/** returns true if this bdd is a valid bdd */
	public final boolean isValid(int bdd) {	return t_nodes[OFFSET_VAR + NODE_WIDTH * bdd] != -1; }

	/** make the node invalid */
	protected final void invalidate(int bdd) {		t_nodes[OFFSET_VAR + NODE_WIDTH * bdd] = -1; }



	// set multiple members (including ref) at the same time. not called very often
	protected final void setAll(final int bdd, final int v, final int l, final int h, final short r) {
		t_nodes[NODE_WIDTH * bdd + OFFSET_VAR]= v;
		t_nodes[NODE_WIDTH * bdd + OFFSET_LOW]= l;
		t_nodes[NODE_WIDTH * bdd + OFFSET_HIGH]= h;
		t_ref[bdd] = r;
	}

	// set multiple members at the same time. not called very often
	protected final void setAll(final int bdd, final int v, final int l, final int h) {
			t_nodes[NODE_WIDTH * bdd + OFFSET_VAR]= v;
			t_nodes[NODE_WIDTH * bdd + OFFSET_LOW]= l;
			t_nodes[NODE_WIDTH * bdd + OFFSET_HIGH]= h;
	}

	/** returns true of the bdd <tt>bdd</tt> is the same as (var,low,high) */
	protected final boolean match_table(final int bdd, final int var, final int low, final int high) {
		// WAS: return getVar(bdd) == var && getLow(bdd) == low && getHigh(bdd) == high;

		final int offset = bdd * NODE_WIDTH;
		return t_nodes[offset + OFFSET_VAR] == var && t_nodes[offset + OFFSET_LOW] == low &&
			t_nodes[offset + OFFSET_HIGH] == high;
	}


	// -----------------------------------------------------------------------------------------
	// low-level access to the linked list
	private final void setNext(int bdd, int v) { t_list[OFFSET_NEXT + LIST_WIDTH * bdd] = v; }
	private final void setPrev(int bdd, int v) { t_list[OFFSET_PREV + LIST_WIDTH * bdd] = v; }
	private final int getNext(final int bdd) {	return t_list[OFFSET_NEXT + LIST_WIDTH * bdd];	}
	private final int getPrev(final int bdd) {	return t_list[OFFSET_PREV + LIST_WIDTH * bdd];	}

	/** a more clever way to set all the prev members up to <tt>upto</tt> to 0 */
	private final void clearPrev(int from, int upto) {
		from = from * LIST_WIDTH + OFFSET_PREV;
		upto = upto * LIST_WIDTH + OFFSET_PREV;

		// TODO: we should unroll this at least once!
		while(from < upto) {
			t_list[from] = 0;
			from += LIST_WIDTH;
		}
	}

	/** put <tt>a</tt> before <tt>b</tt> in the linked list */
	private final void connect_list(int a, int b) {
		final int o1 = a * LIST_WIDTH;
		final int o2 = b * LIST_WIDTH;

		t_list[o1 + OFFSET_NEXT] = t_list[o2 + OFFSET_PREV];
		t_list[o2 + OFFSET_PREV] = a;
	}




	// ----[ node marking ] ----------------------------

	/**
	 * call this functio to enable the fast variant of the mark_node() function.
	 * if you do that, you mustlet JDD know the maximum depth of all trees by calling
	 * tree_depth_changed() from your sub-class
	 * @see #tree_depth_changed
	 */
	public void enableStackMarking() {
		stack_marking_enabled = true;
	}

	/**
	 * recursively mark nodes, used by some internal functions.
	 * @see #mark_node
	 */
	public final void mark_tree(int bdd) {
		if(stack_marking_enabled) {
			mark_tree_stack(bdd);
		} else {
			mark_tree_rec(bdd);
		}
	}

	/** the recursive version f mark_tree */
	private  final void mark_tree_rec(int bdd) {
		if(bdd < 2) {
			return;
		}
		if( isNodeMarked(bdd)) {
			return;
		}
		mark_node(bdd);
		mark_tree( getLow(bdd) );
		mark_tree_rec( getHigh(bdd) );
	}


	/**
	 * non recursive version of mark tree
	 * <p>to use this function, you MUST know the maximum depth of the tree and tell
	 * it to NodeTable by calling tree_depth_changed()
	 * @see #mark_tree_rec
	 * @see #tree_depth_changed
	 * @see #enableStackMarking
	 */
	private final void mark_tree_stack(int bdd) {
		// ok, it works like this:
		// we dont want to do recursive calls in such a tight functions so we do an
		// artifical recursive call by haveing out own stack. the stack is "mark_stack"
		// and it is important to have the right size. this is why the user must call
		// recursive_mark_tree() as soon as the tree depth changes


		// if its terminal, then we are already done
		if(bdd < 2 ) {
			return;
		}

		// insert the first one
		int tos = 0; // top of stack
		mark_stack[tos++] = bdd;
		mark_node(bdd);

		// here we go, recursively mark the nodes in this tree:
		while(tos > 0) {
			final int next = mark_stack[--tos];
			int tmp = getLow(next);
			if( tmp > 1 && !isNodeMarked(tmp)) {
				mark_node(tmp);
				mark_stack[tos++] = tmp;
			}

			tmp = getHigh(next);
			if( tmp > 1 && !isNodeMarked(tmp)) {
				mark_node(tmp);
				mark_stack[tos++] = tmp;
			}
		}
	}



	/** recursively unmark nodes, used by some internal functions */
	public final void unmark_tree(int bdd) {
		if(bdd < 2) {
			return;
		}
		if( !isNodeMarked(bdd)) {
			return;
		}
		unmark_node(bdd);
		unmark_tree( getLow(bdd) );
		unmark_tree( getHigh(bdd) );
	}

	public final void mark_node(int bdd) {
		t_nodes[OFFSET_VAR + NODE_WIDTH*bdd] |= NODE_MARK;
	}

	public final void unmark_node(int bdd) {
		t_nodes[OFFSET_VAR + NODE_WIDTH*bdd] &= NODE_UNMARK;
	}

	public final boolean isNodeMarked(int bdd) {
		return (t_nodes[OFFSET_VAR + NODE_WIDTH*bdd] & NODE_MARK) != 0;
	}

	// ------- [ debug ] -----------------------------------------------------------------------

	/* return the amount of internally allocated memory in bytes */
	public long getMemoryUsage() {
		long ret = 0;

		if (t_nodes!= null) {
			ret += t_nodes.length * 4;
		}
		if (t_list!= null) {
			ret += t_list.length * 4;
		}
		if (t_ref != null) {
			ret += t_ref.length * 2;
		}
		if (work_stack != null) {
			ret += work_stack.length * 4;
		}
		if (mark_stack != null) {
			ret += mark_stack.length * 4;
		}

		return ret;
	}


	/**
	 * count the number of ROOT bdd nodes.
	 *
	 */
	public int countRootNodes() {
		int c = 0;
		for(int i = 0; i < table_size; i++) {
			if(isValid(i) && (getRef(i) > 0 && getRef(i) != MAX_REFCOUNT)) {
				c++;
			}
		}
		return c;
	}

	protected void show_tuple(int i) {
		JDDConsole.out.println("" + i + "\t" + getVar(i) + "\t" + getLow(i) + "\t" + getHigh(i) + "\t: " + getRef(i) );
	}

	protected void show_table() {
		JDDConsole.out.println("Node-table:");
		for(int i = 0; i < table_size; i++) {
			if(isValid(i) ) {
				show_tuple(i);
			}
		}
	}
	protected void show_table_all() {
		JDDConsole.out.println("Node-table (complete):");
		for(int i = 0; i < table_size; i++) {
			show_tuple(i);
		}
	}


	// --------------------------------------------------------------------

	void check() {

		// see if the number of free nodes is correct
		int c = 2, b = 0;
		for(int i = 2; i < table_size; i ++) {
			if(isValid(i) ) {
				c++;
			} else {
				b++;
			}
		}
		Test.check( c == (table_size - free_nodes_count), "Invalid # of free nodes: #live= " +c + ", table_size="+table_size + ", free_nodes_count=" +free_nodes_count);

		// see if a nodes children point to invalid entries:
		for(int i = 0; i < table_size; i ++) {
			if(isValid(i)) {
				if(getLow(i) < 0 || getHigh(i) < 0) {
					show_tuple(i);
					Test.check(false, "Invalied node entry");
				}
				if( ( getLow(i) > 1 && !isValid(getLow(i))  ) || (getHigh(i) > 1 && !isValid( getHigh(i)) )  ) {
					System.err.println();
					show_tuple(i);
					show_tuple(getLow(i) );
					show_tuple(getHigh(i) );
					Test.check(false);
				}
			}
		}

		if(table_size > 100) {
			// out.println("(omitting slow parts of NodeTable.check(), table too large)");
			return;
		}

		// stupid O(N * N) test to see if there are two of any nodes in the table
		for(int i = 0; i < table_size; i ++) {
			if(isValid(i)) {
				for(int j = i + 1; j < table_size; j++) {
					if(getVar(i) == getVar(j) && getLow(i) == getLow(j) && getHigh(i) == getHigh(j)) {
						JDDConsole.out.println("Duplicate entries in NodeTable (" + i + " and " + j +"): ");
						show_tuple(i);
						show_tuple(j);
						System.exit(20);
					}
				}
			}
		}
	}



	// --------------------------------------------------------
	/** show some statistics ... */
	public void showStats() {

		JDDConsole.out.println("NT nodes/free/#grow/grow-time/dead/root: " +
			table_size + "/" + free_nodes_count + "/" + stat_nt_grow + "/" + stat_grow_time +
			"/" + dead_nodes + "/" + countRootNodes() );


		JDDConsole.out.println("HT chain/access: "
		+ ht_chain + "/" + stat_lookup_count);

		JDDConsole.out.println("GC #times/#freed/signal-time/gc-time: " +
			stat_gc_count + "/" + stat_gc_freed + "/" + stat_notify_time + "/" + stat_gc_time );
	}

	// --[ recursive node test operators ]------------------------------------------------------
	private String check_say = null;
	/** check if all nodes are ok. it will test validaty and ref-count of nodes in the table */
	public void check_all_nodes() {
		for(int i = 0; i < work_stack_tos; i++) {
			check_node(work_stack[i]);
		}

		for(int i = 0; i < table_size; i++) {
			if( isValid(i) && getRefPlain(i) > 0 ) {
				check_node(i);
			}
		}
	}

	/** check if some node is ok. it actuallt check the whole tree below the node */
	public void check_node(int node, String str) {
		check_say = str;
		check_node(node);
	}
	private void check_node(int node) {
		if(node < 2) {
			return;
		}
		if(!isValid(node)) {
			show_tuple(node);
			Test.check(false, "Node " + node + " invalid " + ((check_say != null) ? check_say : ""));
		}

		// XXX: this is gode, but we should mark nodes so we dont check them multiple
		//      times if we are doing anything recursive!
		// check_node( getLow(node));
		// check_node( getHigh(node));
	}

	private int count_free_nodes() {
		int ret = 0, root = first_free_node;
		while(root != 0) {
			ret++;
			root = getNext(root);
		}
		return ret;
	}

	// -------------- [testbed] ----------------------------
	/** testbench. do not call */
	public static void internal_test() {
		Test.start("NodeTable");

		NodeTable nt = new NodeTable(10);
		// nt.show_table(); nt.show_unused();


		// NOT WORKING ANYMORE
		// Test.check(nt.table_size == 10 && nt.free_nodes_tos == 8, "Table ok before grow");
		nt.add(4,0,1);
		Test.check(nt.table_size == nt.free_nodes_count  + 3, "Table ok after grow"); // bad test, I know
		nt.check();


		// now, this is not a test, its just for profiling huge grows:
		final int MAX = 15;
		nt = new NodeTable(MAX);
		int last = 0;
		for(int i = 2; i < MAX; i++) {
			last = nt.add(i , last, last);
		}
		nt.check();
		nt.grow();	nt.check();
		nt.grow();	nt.check();
		nt.grow();	nt.check();


		// test the hash-table stuff
		nt = new NodeTable(10);
		// save by work_stack
		final int a = nt.add(4,0,1);
		nt.work_stack[0] = a;
		nt.work_stack_tos++;

		// save by ref
		final int b = nt.add(4,1,0);
		nt.ref(b);

		// dont save:
		final int c = nt.add(3,0,1);
		Test.checkEquality( nt.count_free_nodes(), nt.free_nodes_count, "free node count correct (1)");

		nt.gc();
		Test.check( nt.isValid( a), "saved by work_stack");
		Test.check( nt.isValid( b), "saved by ref");
		Test.check(!nt.isValid( c), "should have been removed");
		Test.checkEquality( nt.count_free_nodes(), nt.free_nodes_count, "free node count correct (2)");

		nt.grow();
		Test.check( nt.isValid( a), "saved by work_stack");
		Test.check( nt.isValid( b), "saved by ref");
		Test.check(!nt.isValid( c), "should have been removed");
		Test.checkEquality( nt.count_free_nodes(), nt.free_nodes_count, "free node count correct (3)");

		Test.end();
	}

}
