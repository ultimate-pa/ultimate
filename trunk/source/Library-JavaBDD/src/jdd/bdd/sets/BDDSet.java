
package jdd.bdd.sets;

import jdd.bdd.*;
import jdd.util.*;
import jdd.util.sets.*;

/** BDD representation of a set (of a product of few small subsets) */

public class BDDSet implements Set {
	private BDDUniverse universe;
	private boolean [] internal_minterm;
	/* package */ int bdd;

	/* package */ BDDSet(BDDUniverse u, int bdd) {
		this.universe = u;
		this.bdd = universe.ref(bdd);
		this.internal_minterm = new boolean[ universe.numberOfBits() ];
	}

	public double cardinality() { return universe.satCount(bdd); }
	public void free() { universe.deref(bdd);	}
	public boolean equals(Set s) { return bdd == ((BDDSet)s).bdd; }

	public boolean isEmpty() { return bdd == 0; }

	public void assign(Set s) {
		universe.deref(bdd);
		bdd = universe.ref(((BDDSet)s).bdd);
	}
	public void clear() {
		universe.deref(bdd);
		bdd = 0;
	}

	/* package */ void show() { universe.printSet(bdd); }

	/** returns true if assignment is in the set. allows dont cares */
	public boolean memberDC(int [] assignment) {
		int x = universe.vectorToBDD(assignment);
		int tmp = universe.or(x, bdd);
		boolean ret = (tmp == bdd);
		universe.deref(x);
		return ret;
	}

	/** fast membership test. no dont cares */
	public boolean member(int [] assignment) {
		universe.vectorToMinterm(assignment, internal_minterm);
		return universe.member(bdd, internal_minterm);
	}

	/** returns true if assignment was in the set */
	public boolean remove(int [] assignment) {
		int x = universe.vectorToBDD(assignment);
		int notx = universe.ref( universe.not( x) );
		universe.deref(x);
		int tmp = universe.ref( universe.and( bdd, notx) );
		universe.deref(notx);
		if(tmp == bdd) { // alread in there??
			universe.deref(tmp);
			return false;
		} else {
			universe.deref(bdd);
			bdd = tmp;
			return true;
		}
	}


	/** returns true if assignment was not alread in the set */
	public boolean insert(int [] assignments) {
		int x = universe.vectorToBDD(assignments);
		int tmp = universe.ref( universe.or( bdd, x) );

		if(tmp == bdd) { // alread in there??
			universe.deref(tmp);
			return false;
		} else {
			universe.deref(bdd);
			bdd = tmp;
			return true;
		}
	}

	public Set copy() { return new BDDSet(universe, bdd); }
	public Set invert() {
		int neg = universe.ref( universe.not(bdd) );
		BDDSet ret = new BDDSet(universe, universe.removeDontCares(neg) );
		universe.deref( neg);
		return ret;
	}

	public Set union(Set s) { return new BDDSet(universe, universe.or(bdd, ((BDDSet)s).bdd) ); }
	public Set intersection(Set s) { return new BDDSet(universe, universe.and(bdd, ((BDDSet)s).bdd) ); }

	public Set diff(Set s_) {
		BDDSet s = (BDDSet) s_;
		int neg = universe.ref( universe.not(s.bdd) );
		int d   = universe.and(bdd, neg);
		universe.deref(neg);
		return new BDDSet(universe, d);
	}


	/** retruns 0 if equal, -1 if this \subset s, +1 if s \subset this, Integer.MAX_VALUE otherwise */
	public int compare(Set s_) {
		BDDSet s = (BDDSet) s_;
		if(s.bdd == bdd) return 0;
		int u = universe.or(bdd, s.bdd);
		if(u == bdd) return +1;
		if(u == s.bdd) return -1;

		return Integer.MAX_VALUE; // no relation between this and s
	}

	public SetEnumeration elements() {
		return new BDDSetEnumeration(universe, bdd);
	}

	public void show(String name) {
		JDDConsole.out.print(name + " = " );
		if(bdd == 0) {	JDDConsole.out.println("empty set");	return;		}

		JDDConsole.out.print("{\n  ");
		SetEnumeration se = elements();
		int j = 0;
		for(; se.hasMoreElements();) {
			int [] x = se.nextElement();
			universe.print(x);
			j += x.length + 1;
			if(j > 20) {
				j = 0;
				JDDConsole.out.print("\n  ");
			} else 	JDDConsole.out.print(" ");
		}
		if(j != 0) JDDConsole.out.println();
		JDDConsole.out.println("\r}");
		se.free();
	}

	// ----------------------------------------------------------------------------------

	static int [] dum = { 3, 4, 5 , 2};
	/** testbench. do not call */
	public static void internal_test() {
		Test.start("BDDSet");

		BDDUniverse u = new BDDUniverse(dum);
		Set s1 = u.createEmptySet();
		Set s2 = u.createFullSet();


		// test insert, remove and member
		int [] v = new int[4];
		v[0] = v[1] = v[2] = v[3] = 0;

		Test.check(s1.insert(v), "v not in S1 before");
		Test.check(!s1.insert(v), "v in S1 after");
		Test.checkEquality( s1.cardinality(), 1.0, "Cardinality 1 after inserting v");
		Test.check(s1.member(v), "v \\in S1");
		Test.check(s1.remove(v), "v removed from S1");
		Test.check(!s1.member(v), "v \\not\\in S1");
		Test.check(!s1.remove(v), "v already removed from S1 and not in S1 anymore");
		Test.checkEquality( s1.cardinality(), 0.0, "S1 empty again");

		// check empty and clear:
		Test.check( s1.isEmpty(), "S1 is empty");
		Test.check(!s2.isEmpty(), "S2 is not empty");

		// test invert
		Set s1_neg = s1.invert();
		Test.check( s1_neg.equals( s2), "(NOT  emptyset) = fullset");
		s1_neg.free();

		// test copy:
		Set s2_copy = s2.copy();
		Test.check( s2_copy.equals( s2), "copy() test");

		// ...and clear
		s2_copy.clear();
		Test.check( s2_copy.equals( s1), "clear() test");
		s2_copy.free();


		// check union
		Set x0 = u.createEmptySet();
		Set x1 = u.createEmptySet();
		Set x10 = u.createEmptySet();

		v[0] = v[1] = v[2] = v[3] = 0; x0.insert(v); x10.insert(v);
		v[0] = v[1] = v[2] = v[3] = 1; x1.insert(v); x10.insert(v);
		Set union = x1.union(x0);
		Test.check(union.equals( x10), "union() - test");
		union.free();

		// check diff:
		Set diff1 = x10.diff( x1);
		Set diff2 = x10.diff( x0);
		Test.check(diff1.equals( x0), "diff() - test 1");
		Test.check(diff2.equals( x1), "diff() - test 2");
		diff1.free();
		diff2.free();

		// check intersection
		Set int1 = x10.intersection( x1);
		Set int2 = x10.intersection( x0);
		Test.check(int1.equals( x1), "intersection() - test 1");
		Test.check(int2.equals( x0), "intersection() - test 2");
		int1.free();
		int2.free();


		// check compare:
		Test.checkEquality( x1.compare(x1), 0, "x1 = x1");
		Test.checkEquality( x10.compare(x1), +1, "x1  < x10");
		Test.checkEquality( x1.compare(x10), -1, "x10 > x1");

		Test.checkEquality( x10.compare(x0), +1, "x10 > x0");
		Test.checkEquality( x0.compare(x10), -1, "x0  < x0");

		Test.checkEquality( x1.compare(x0), Integer.MAX_VALUE , "x10 ?? x0"); // no relation


		s1.free();
		s2.free();

		Test.end();
	}
}
