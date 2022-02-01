

package jdd.bdd.sets;


import jdd.util.Test;
import jdd.util.sets.Set;
import jdd.util.sets.SetEnumeration;


/**
 * Enumerator for the BDD-sets.
 * <p> Notice the very important <tt>free</tt> function !
 */
public class BDDSetEnumeration implements SetEnumeration {
	private final BDDUniverse universe;
	private int bdd;
	private final int [] vec;

	/** You should not call this constructor directly, <tt>Set</tt> should do that job for you!*/
	/* package */ BDDSetEnumeration(BDDUniverse u, int bdd) {
		universe = u;
		this.bdd      = bdd;
		vec      = new int[ universe.subdomainCount() ];
		universe.ref(bdd);
	}

	/** it is very important that you call this function when you are done with the set! */

	@Override
	public void free() {
		universe.deref(bdd);
		bdd = 0;
	}

	@Override
	public boolean hasMoreElements() { return bdd != 0; }

	@Override
	public int [] nextElement() {

		universe.satOneVector(bdd, vec);
		final int sat1 = universe.ref( universe.vectorToBDD(vec));
		final int not_sat1 = universe.ref( universe.not(sat1));
		universe.deref( sat1);
		final int tmp = universe.ref( universe.and(not_sat1, bdd) );
		universe.deref(not_sat1);
		universe.deref(bdd);
		bdd = tmp;

		return vec;

	}

	static int [] dom = { 10,20,30, 40, 50, 60 };
	/** testbench. do not call */
	public static void internal_test() {

		Test.start("SetEnumeration");

		final BDDUniverse u = new BDDUniverse(dom);
		final Set set = u.createEmptySet();


		final int [] val = new int[dom.length];
		int real_size = 0;
		for(int i = 0; i < 200; i++) {
			for(int j = 0; j < dom.length; j++) {
				val[j] = (int)( Math.random() * dom[j]);
			}
			if(set.insert(val)) {
				real_size++;
			}
		}

		Test.checkEquality(real_size, set.cardinality(), "# of elemnets inserted equals set cardinality");


		final Set set2 = set.copy();
		final SetEnumeration se = set.elements();
		int had = 0;
		while(se.hasMoreElements() ) {
			had++;
			final int [] v = se.nextElement();
			Test.check( set2.remove(v) , " returned element really in set");
		}

		Test.checkEquality(real_size, set.cardinality(), "# of elemnets inserted still equals set cardinality");
		Test.checkEquality(had, set.cardinality(), "right number of elements in set");
		Test.checkEquality(set2.cardinality(), 0, "right number of elements in set (Same as above)");

		set2.free();
		set.free();
		se.free();

		Test.end();
	}
}
