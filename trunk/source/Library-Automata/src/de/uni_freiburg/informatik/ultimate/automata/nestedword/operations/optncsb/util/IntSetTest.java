package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.Random;

public class IntSetTest {

	public static void main(final String[] args) {

		final IntSetBits bits = new IntSetBits();
		final IntSetTIntSet tIntSets = new IntSetTIntSet();
		final IntSetHashSet hashSets = new IntSetHashSet();
		final IntSetTreeSet treeSets = new IntSetTreeSet();

		final int num = 9100_000;

		final Random random = new Random(System.currentTimeMillis());
		for (int i = 0; i < num; i++) {
			if (random.nextBoolean()) {
				bits.set(i);
				tIntSets.set(i);
				hashSets.set(i);
				treeSets.set(i);
			}
		}

		System.out.println("test bits");
		testIterator(bits);
		final IntSetBits cpb = (IntSetBits) bits.clone();
		cpb.set(7000_000 - 1);
		testEq(bits, cpb);
		testSubset(bits, cpb);

		System.out.println("test TIntSet");
		testIterator(tIntSets);
		final IntSetTIntSet cpi = (IntSetTIntSet) tIntSets.clone();
		cpi.set(7000_000 - 1);
		testEq(tIntSets, cpi);
		testSubset(tIntSets, cpi);

		System.out.println("test HashSet");
		testIterator(hashSets);
		final IntSetHashSet cph = (IntSetHashSet) hashSets.clone();
		cph.set(7000_000 - 1);
		testEq(hashSets, cph);
		testSubset(hashSets, cph);

		System.out.println("test TreeSet");
		testIterator(treeSets);
		final IntSetTreeSet cpt = (IntSetTreeSet) treeSets.clone();
		cpt.set(7000_000 - 1);
		testEq(treeSets, cpt);
		testSubset(treeSets, cpt);
	}

	private static void testIterator(final IntSet set) {
		final IntIterator iter = set.iterator();
		final long start = System.currentTimeMillis();
		int num = 0;
		while (iter.hasNext()) {
			iter.next();
			num++;
		}
		final long end = System.currentTimeMillis();
		System.out.println("<iter> time = " + (end - start) + " num=" + num);
	}

	private static void testEq(final IntSet a, final IntSet b) {
		final long start = System.currentTimeMillis();
		System.out.println("isEq = " + a.contentEq(b));
		final long end = System.currentTimeMillis();
		System.out.println("<eq> time = " + (end - start));
	}

	private static void testSubset(final IntSet a, final IntSet b) {
		final long start = System.currentTimeMillis();
		System.out.println("isSubset = " + a.subsetOf(b));
		final long end = System.currentTimeMillis();
		System.out.println("<subset> time = " + (end - start));
	}

}
