package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

/**
 * TODO: Moved the main method from CDD to this class; make unit tests from it.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CddTest {

	// XXX: Testing
	public static void main(final String[] args) {
		final CDD a = BooleanDecision.create("a");
		final CDD b = BooleanDecision.create("b");
		final CDD c = BooleanDecision.create("c");
		final CDD d = BooleanDecision.create("d");

		// CDD main = ((a.and(b)).and(c.or(d))).or(e).or(f.negate());
		// CDD main2 = ((a.and(b)).or(a.negate().and(b.negate())));
		// CDD main = main2.or(c.and(d));
		// CDD main = c.or(main2);

		// CDD teil1 = a.negate().and(b).and(c);
		// CDD teil2 = a.and(b);
		// CDD main = teil1.or(teil2);

		// CDD links = a.negate().or(b.or(c));
		// CDD rechts = a.or(b);
		// CDD main = links.and(rechts);
		// CDD links = a.negate().and(b.and(c));
		// CDD rechts = a.and(d);
		// CDD main = links.or(rechts);
		final CDD links = a.negate().and(b);
		final CDD rechts = a.and(b.or(c)).and(d);
		final CDD main = links.or(rechts);

		final CDD test = a.negate();
		final CDD test2 = a.or(b);

		System.out.println("********************************* CDD ********************************* ");
		System.out.println(main.toString());
		System.out.println(main.toTexString());
		testIsAtomic(test);
		testIsAtomic(test2);
		testIsAtomic(links);
		testIsAtomic(main);
		testIsAtomic(a);

		final CDD[] dnf = main.toDNF();
		System.out.println("********************************* DNF ********************************* ");

		for (int i = 0; i < dnf.length; i++) {
			System.out.println("*** Conjunctive term " + i + ": ");
			System.out.println(dnf[i].toString());
		}

		final CDD[] cnf = main.toCNF();
		System.out.println("********************************* CNF ********************************* ");

		for (int i = 0; i < cnf.length; i++) {
			System.out.println("*** Disjunctive term " + i + ": ");
			System.out.println(cnf[i].toString());
		}

		System.out.println("*********************************************************************** ");
	}

	private static void testIsAtomic(final CDD cdd) {
		System.out.println("The formula " + cdd.toString() + " is atomic: " + cdd.isAtomic());
	}
}
