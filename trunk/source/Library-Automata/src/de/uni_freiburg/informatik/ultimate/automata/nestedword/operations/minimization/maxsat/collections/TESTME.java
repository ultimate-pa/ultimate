package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

public class TESTME {
	public static void main(final String[] args) {
		final ScopedTransitivityGenerator<String> rtg = new ScopedTransitivityGenerator<>(false);
		for (int i = 0; i < 10; ++i) {
			rtg.addContent("x" + i);
		}
		System.out.println("       \n-------\n-- 1 --\n-------\n       ");
		// no backtracking
		azzert(rtg, "x1", "x2");
		azzert(rtg, "x3", "x2");
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x5", "x6");
		azzert(rtg, "x6", "x7");
		azzert(rtg, "x1", "x7");
		
		revert(rtg);
		
		System.out.println("       \n-------\n-- 2 --\n-------\n       ");
		// same with backtracking
		azzert(rtg, "x1", "x2");
		azzert(rtg, "x3", "x2");
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x5", "x6");
		azzert(rtg, "x6", "x7");
		azzert(rtg, "x1", "x7");
		
		revert(rtg);
		
		System.out.println("       \n-------\n-- 3 --\n-------\n       ");
		// backtracking twice
		azzert(rtg, "x1", "x2");
		azzert(rtg, "x3", "x2");
		newScope(rtg);
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x3", "x4");
		revert(rtg);
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x5", "x6");
		
		azzert(rtg, "x6", "x7");
		azzert(rtg, "x1", "x7");
		
		revert(rtg);
		
		System.out.println("       \n-------\n-- 4 --\n-------\n       ");
		// persistent
		azzert(rtg, "x1", "x2");
		azzert(rtg, "x3", "x2");
		azzert(rtg, "x3", "x4");
		makePersistent(rtg);
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x5", "x6");
		azzert(rtg, "x6", "x7");
		azzert(rtg, "x1", "x7");
		revert(rtg);
		azzert(rtg, "x1", "x2");
		azzert(rtg, "x3", "x2");
		azzert(rtg, "x3", "x4");
		azzert(rtg, "x3", "x5");
	}
	
	private static void revert(final ScopedTransitivityGenerator<String> rtg) {
		System.out.println("reverting");
		rtg.revertOneScope();
	}

	private static void newScope(final ScopedTransitivityGenerator<String> rtg) {
		System.out.println("adding scope");
		rtg.addScope();
	}
	
	private static void makePersistent(final ScopedTransitivityGenerator<String> rtg) {
		System.out.println("making persistent");
		rtg.makeAllScopesPersistent();
	}
	
	private static void azzert(final ScopedTransitivityGenerator<String> rtg, final String x1, final String x2) {
		System.out.println(String.format("asserting %s = %s", x1, x2));
		final Doubleton<String> doubleton = new Doubleton<String>(x1, x2);
		final Iterable<Doubleton<String>> iterable = rtg.assertEquality(doubleton);
		
		final Iterator<Doubleton<String>> iterator = iterable.iterator();
		if (!iterator.hasNext()) {
			System.out.println("nothing");
		} else {
			do {
				System.out.println(iterator.next());
			} while (iterator.hasNext());
		}
	}
}
