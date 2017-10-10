package de.uni_freiburg.informatik.ultimate.util;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.datastructures.AbstractCCElementFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;

public class CongruenceClosureTest {

	/**
	 * Test about basic congruence closure operations.
	 */
	@Test
	public void test01() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCcElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCcElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		// reflexivity
		assertTrue(cc.getEqualityStatus(x, x) == EqualityStatus.EQUAL);

		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.UNKNOWN);

		cc.reportEquality(x, z);

		// symmetry
		assertTrue(cc.getEqualityStatus(z, x) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(x, z) == EqualityStatus.EQUAL);

		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.UNKNOWN);

		cc.reportEquality(x, y);

		assertFalse(cc.isInconsistent());

		// transitivity
		assertTrue(cc.getEqualityStatus(y, z) == EqualityStatus.EQUAL);

		// congruence (forward)
		assertTrue(cc.getEqualityStatus(f_x, f_y) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_x, f_z) == EqualityStatus.EQUAL);


		assertTrue(cc.getEqualityStatus(f_x, g_x) == EqualityStatus.UNKNOWN);

		cc.reportEquality(f, g);

		assertFalse(cc.isInconsistent());
		assertTrue(cc.getEqualityStatus(f_x, g_x) == EqualityStatus.EQUAL);
	}

	@Test
	public void test02() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCcElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCcElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		cc.reportEquality(x, z);

		assertTrue(cc.getEqualityStatus(x, z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(y, z) == EqualityStatus.UNKNOWN);
		assertTrue(cc.getEqualityStatus(f_x, f_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(g_x, g_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_x, g_z) == EqualityStatus.UNKNOWN);

		cc.reportEquality(f_y, z);

		assertTrue(cc.getEqualityStatus(f_y, z) == EqualityStatus.EQUAL);

		cc.reportEquality(f_x, g_z);

		assertTrue(cc.getEqualityStatus(f_x, g_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_z, g_x) == EqualityStatus.EQUAL);

		cc.reportEquality(x, y);

		assertTrue(cc.getEqualityStatus(x, g_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(y, f_y) == EqualityStatus.EQUAL);
	}


	@Test
	public void test03() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCcElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCcElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		cc.reportDisequality(f_x, f_y);
		assertTrue(cc.getEqualityStatus(f_x, f_y) == EqualityStatus.NOT_EQUAL);
		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.NOT_EQUAL);

	}

	@Test
	public void test04() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCcElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCcElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		cc.reportEquality(f, g);
		assertTrue(cc.getEqualityStatus(f_x, g_x) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_y, g_y) == EqualityStatus.EQUAL);

	}

	/**
	 * example:
	 * <ul>
	 *  <li> preState:
	 *   (i = f(y)) , (j != f(x))
	 *  <li> then introduce equality (i = j)
	 *  <li> we should get the output state, i.e., we have to propagate an extra disequality on introducing the equality
	 *   (i = f(y)) , (j != f(x)), (i = j), (x != y)
	 * </ul>
	 */
	@Test
	public void test05() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCcElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);

		final StringCcElement i = factory.getBaseElement("i");
		cc.getRepresentativeAndAddElementIfNeeded(i);
		final StringCcElement j = factory.getBaseElement("j");
		cc.getRepresentativeAndAddElementIfNeeded(j);

		cc.reportEquality(i, f_y);
		cc.reportDisequality(j, f_x);
		cc.reportEquality(i, j);

		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.NOT_EQUAL);

	}

	/**
	 * say we knew before
	 * f(x1, x2) != g(y1, y2), and f = g
	 * now we are reporting x1 = y1
	 * --> then we need to propagate  x2 != y2 now.
	 */
	@Test
	public void test06() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x1 = factory.getBaseElement("x1");
		cc.getRepresentativeAndAddElementIfNeeded(x1);
		final StringCcElement x2 = factory.getBaseElement("x2");
		cc.getRepresentativeAndAddElementIfNeeded(x2);
		final StringCcElement y1 = factory.getBaseElement("y1");
		cc.getRepresentativeAndAddElementIfNeeded(y1);
		final StringCcElement y2 = factory.getBaseElement("y2");
		cc.getRepresentativeAndAddElementIfNeeded(y2);

		final StringCcElement f_x1_x2 = factory.getFuncAppElement(f, x1, x2);
		cc.getRepresentativeAndAddElementIfNeeded(f_x1_x2);
		final StringCcElement g_y1_y2 = factory.getFuncAppElement(g, y1, y2);
		cc.getRepresentativeAndAddElementIfNeeded(g_y1_y2);


		cc.reportDisequality(f_x1_x2, g_y1_y2);
		cc.reportEquality(f, g);

		cc.reportEquality(x1, y1);

		assertTrue(cc.getEqualityStatus(x2, y2) == EqualityStatus.NOT_EQUAL);
	}

	/**
	 * Tests what happens when we don't register all nodes up front (i.e. before the first report*-call).
	 */
	@Test
	public void test07() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement f_a = factory.getFuncAppElement(f, a);
		final StringCcElement f_b = factory.getFuncAppElement(f, b);

		cc.reportEquality(a, b);

//		assertTrue(cc.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);

		cc.reportDisequality(f_a, f_b);

		assertTrue(cc.isInconsistent());

	}

	@Test
	public void test07a() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement f_a_b = factory.getFuncAppElement(f, a, b);
		final StringCcElement g_b_a = factory.getFuncAppElement(g, b, a);

		cc.reportEquality(a, b);

		cc.reportEquality(f, g);

		cc.reportDisequality(f_a_b, g_b_a);

		assertTrue(cc.isInconsistent());

	}

	/**
	 * Test for debugging the congruence propagation done in CongruenceClosure.registerNewElement(..). Checks if the
	 * argument order is accounted for.
	 */
	@Test
	public void test07b() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement i = factory.getBaseElement("i");
		final StringCcElement j = factory.getBaseElement("j");

		final StringCcElement f_a_i = factory.getFuncAppElement(f, a, i);
		final StringCcElement g_j_b = factory.getFuncAppElement(g, j, b);

		cc.reportEquality(a, b);
		cc.reportEquality(i, j);

		cc.reportEquality(f, g);

		/*
		 * At this point we _cannot_ propagate "f(a,i) = g(j,b)" because of argument order. (We could propagate
		 * f(a,i) = g(b,j)..)
		 */
		cc.reportDisequality(f_a_i, g_j_b);

		assertFalse(cc.isInconsistent());
	}


	/**
	 * Example from Jochen Hoenicke's Decision Procedures lecture.
	 *
	 */
	@Test
	public void test08() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");

		final StringCcElement f_a_b = factory.getFuncAppElement(f, a, b);

		final StringCcElement f_f_a_b_b = factory.getFuncAppElement(f, f_a_b, b);

		cc.reportEquality(f_a_b, a);
		assertFalse(cc.isInconsistent());

		cc.reportDisequality(f_f_a_b_b, a);
		assertTrue(cc.isInconsistent());
	}

	/**
	 * Example from Jochen Hoenicke's Decision Procedures lecture.
	 */
	@Test
	public void test09() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement f_a = factory.getFuncAppElement(f, a);
		final StringCcElement f2_a = factory.getFuncAppElement(f, f_a);
		final StringCcElement f3_a = factory.getFuncAppElement(f, f2_a);
		final StringCcElement f4_a = factory.getFuncAppElement(f, f3_a);
		final StringCcElement f5_a = factory.getFuncAppElement(f, f4_a);

		cc.reportEquality(f3_a, a);
		cc.reportEquality(f5_a, a);

		cc.reportDisequality(f_a, a);
		assertTrue(cc.isInconsistent());
	}


	/**
	 * Tests the (quasi-)lattice operations join, meet, isStrongerThan.
	 * Only introduces equalities, no disequalities.
	 */
	@Test
	public void testOperators1() {
		final CongruenceClosure<StringCcElement> cc1 = new CongruenceClosure<>();
		final CongruenceClosure<StringCcElement> cc2 = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");

		final StringCcElement i = factory.getBaseElement("i");
		final StringCcElement j = factory.getBaseElement("j");

		final StringCcElement x = factory.getBaseElement("x");
		final StringCcElement y = factory.getBaseElement("y");

		final StringCcElement f_a = factory.getFuncAppElement(f, a);
		final StringCcElement f_f_a = factory.getFuncAppElement(f, f_a);
		final StringCcElement f_b = factory.getFuncAppElement(f, b);
		final StringCcElement f_f_b = factory.getFuncAppElement(f, f_b);


		cc1.reportEquality(a, b);
		cc1.reportEquality(f_f_a, j);
		cc1.reportEquality(x, y);
		cc1.reportEquality(i, j);
		cc1.reportEquality(i, x);
		cc1.getRepresentativeAndAddElementIfNeeded(f_f_b);
		// state of cc1 should be {{a,b}, {f(a), f(b)}, {i,j,x,y,f(f(a)), f(f(b))}}
		assertTrue(cc1.getEqualityStatus(a, b) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(i, f_f_b) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(y, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(y, j) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(b, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc1.getEqualityStatus(a, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc1.getEqualityStatus(a, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc1.getEqualityStatus(a, f_f_a) == EqualityStatus.UNKNOWN);


		cc2.reportEquality(i, x);
		cc2.reportEquality(f_a, f_b);
		cc2.reportEquality(f_f_a, b);
		cc2.reportEquality(f_f_a, a);
		// state of cc2 should be {{a, b, f(f(a))}, {i,x} {f(a), f(b)}} (the element f_f_b is not known to cc2)
		assertTrue(cc2.getEqualityStatus(a, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(b, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(i, x) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(i, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc2.getEqualityStatus(a, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc2.getEqualityStatus(x, f_f_a) == EqualityStatus.UNKNOWN);


		// cc1 and cc2 should be incomparable
		assertFalse(cc1.isStrongerThan(cc2));
		assertFalse(cc2.isStrongerThan(cc1));

		final CongruenceClosure<StringCcElement> cc3 = cc1.join(cc2);
		// state of cc3 should be {{a, b}, {i,x} {f(a), f(b)}, {f(f(a)), f(f(b))}}
		assertTrue(cc3.getEqualityStatus(a, b) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(i, x) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(f_f_a, f_f_b) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(b, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_a, x) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_f_a, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_f_a, x) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_f_a, a) == EqualityStatus.UNKNOWN);

		// cc3 should be strictly weaker than both cc1 and cc2
		assertTrue(cc1.isStrongerThan(cc3));
		assertFalse(cc3.isStrongerThan(cc1));
		assertTrue(cc2.isStrongerThan(cc3));
		assertFalse(cc3.isStrongerThan(cc2));

		final CongruenceClosure<StringCcElement> cc4 = cc1.meet(cc2);
		// state of cc4 should be {{a, b, i, j, x, y, f(f(a)), f(f(b))}, {f(a), f(b)}}
		assertTrue(cc4.getEqualityStatus(a, b) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(b, i) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(i, j) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(x, y) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(y, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(f_f_b, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(f_b, f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(b, f_b) == EqualityStatus.UNKNOWN);

		// cc3 should be strictly stronger than both cc1 and cc2
		assertTrue(cc4.isStrongerThan(cc1));
		assertFalse(cc1.isStrongerThan(cc4));
		assertTrue(cc4.isStrongerThan(cc2));
		assertFalse(cc2.isStrongerThan(cc4));
	}

	/*
	 * TODO (collections of things that could be tested specifically)
	 * Test the alignment of the known elements that has to happen before the operations.
	 */

	/**
	 * Tests the (quasi-)lattice operations join, meet, isStrongerThan.
	 * Exactly like test testOperators1, except for one disequality (which does not introduce a contradiction, but needs
	 * to be handled by join and meet
	 */
	@Test
	public void testOperators2() {
		final CongruenceClosure<StringCcElement> cc1 = new CongruenceClosure<>();
		final CongruenceClosure<StringCcElement> cc2 = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");

		final StringCcElement i = factory.getBaseElement("i");
		final StringCcElement j = factory.getBaseElement("j");

		final StringCcElement x = factory.getBaseElement("x");
		final StringCcElement y = factory.getBaseElement("y");

		final StringCcElement f_a = factory.getFuncAppElement(f, a);
		final StringCcElement f_f_a = factory.getFuncAppElement(f, f_a);
		final StringCcElement f_b = factory.getFuncAppElement(f, b);
		final StringCcElement f_f_b = factory.getFuncAppElement(f, f_b);


		cc1.reportEquality(a, b);
		cc1.reportEquality(f_f_a, j);
		cc1.reportEquality(x, y);
		cc1.reportEquality(i, j);
		cc1.reportEquality(i, x);
		cc1.getRepresentativeAndAddElementIfNeeded(f_f_b);
		// state of cc1 should be {{a,b}, {f(a), f(b)}, {i,j,x,y,f(f(a)), f(f(b))}}
		assertTrue(cc1.getEqualityStatus(a, b) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(i, f_f_b) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(y, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(y, j) == EqualityStatus.EQUAL);
		assertTrue(cc1.getEqualityStatus(b, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc1.getEqualityStatus(a, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc1.getEqualityStatus(a, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc1.getEqualityStatus(a, f_f_a) == EqualityStatus.UNKNOWN);


		cc2.reportEquality(i, x);
		cc2.reportEquality(f_a, f_b);
		cc2.reportEquality(f_f_a, b);
		cc2.reportEquality(f_f_a, a);
		cc2.reportDisequality(f_b, x); // ONLY CHANGE to testOperators1 in terms of constraints in cc1 and cc2
		// state of cc2 should be {{a, b, f(f(a))}, {i,x} {f(a), f(b)}}, x != f(a) (element f_f_b is not known to cc2)
		assertTrue(cc2.getEqualityStatus(a, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(b, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(i, x) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(x, f_a) == EqualityStatus.NOT_EQUAL);
		assertTrue(cc2.getEqualityStatus(a, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc2.getEqualityStatus(x, f_f_a) == EqualityStatus.UNKNOWN);


		// cc1 and cc2 should be incomparable
		assertFalse(cc1.isStrongerThan(cc2));
		assertFalse(cc2.isStrongerThan(cc1));

		final CongruenceClosure<StringCcElement> cc3 = cc1.join(cc2);
		// state of cc3 should be {{a, b}, {i,x} {f(a), f(b)}, {f(f(a)), f(f(b))}} (unchanged from testOperators1)
		assertTrue(cc3.getEqualityStatus(a, b) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(i, x) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(f_f_a, f_f_b) == EqualityStatus.EQUAL);
		assertTrue(cc3.getEqualityStatus(b, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_a, x) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_f_a, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_f_a, x) == EqualityStatus.UNKNOWN);
		assertTrue(cc3.getEqualityStatus(f_f_a, a) == EqualityStatus.UNKNOWN);

		// cc3 should be strictly weaker than both cc1 and cc2
		assertTrue(cc1.isStrongerThan(cc3));
		assertFalse(cc3.isStrongerThan(cc1));
		assertTrue(cc2.isStrongerThan(cc3));
		assertFalse(cc3.isStrongerThan(cc2));

		final CongruenceClosure<StringCcElement> cc4 = cc1.meet(cc2);
		// state of cc4 should be {{a, b, i, j, x, y, f(f(a)), f(f(b))}, {f(a), f(b)}}, x != f(a)
		// (includes the extra disequality from cc2, in comparison to testOperators1)
		assertTrue(cc4.getEqualityStatus(a, b) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(b, i) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(i, j) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(x, y) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(y, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(f_f_b, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(f_b, f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(x, f_a) == EqualityStatus.NOT_EQUAL);
		assertTrue(cc4.getEqualityStatus(b, f_b) == EqualityStatus.NOT_EQUAL);

		// cc3 should be strictly stronger than both cc1 and cc2
		assertTrue(cc4.isStrongerThan(cc1));
		assertFalse(cc1.isStrongerThan(cc4));
		assertTrue(cc4.isStrongerThan(cc2));
		assertFalse(cc2.isStrongerThan(cc4));

	}


	@Test
	public void testRemove01() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement c = factory.getBaseElement("c");

		cc.reportEquality(a, b);
		cc.reportEquality(b, c);
		assertTrue(cc.getEqualityStatus(a, c) == EqualityStatus.EQUAL);
		cc.removeSimpleElement(b);
		assertTrue(cc.getEqualityStatus(a, c) == EqualityStatus.EQUAL);
		cc.getRepresentativeAndAddElementIfNeeded(b);
		assertTrue(cc.getEqualityStatus(a, b) == EqualityStatus.UNKNOWN);
	}

	@Test
	public void testRemove02() {
		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement c = factory.getBaseElement("c");

		final StringCcElement f_a = factory.getOrConstructFuncAppElement(f, a);
		final StringCcElement f_b = factory.getOrConstructFuncAppElement(f, b);
		final StringCcElement f_c = factory.getOrConstructFuncAppElement(f, c);

		cc.reportEquality(a, b);
		cc.reportEquality(b, c);
		cc.getRepresentativeAndAddElementIfNeeded(f_a);
		cc.getRepresentativeAndAddElementIfNeeded(f_b);
		cc.getRepresentativeAndAddElementIfNeeded(f_c);
		assertTrue(cc.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_c, f_b) == EqualityStatus.EQUAL);
		cc.removeSimpleElement(b);
		assertTrue(cc.getEqualityStatus(f_a, f_c) == EqualityStatus.EQUAL);
		cc.getRepresentativeAndAddElementIfNeeded(f_b);
		assertTrue(cc.getEqualityStatus(f_a, f_b) == EqualityStatus.UNKNOWN);
	}



	// TODO test transformer

}

class StringElementFactory extends AbstractCCElementFactory<StringCcElement, String> {

	@Override
//	protected StringCcElement newBaseElement(final String c, final boolean isFunction) {
	protected StringCcElement newBaseElement(final String c) {
		return new StringCcElement(c);
	}

	public StringCcElement getFuncAppElement(final StringCcElement f, final StringCcElement... args) {
		return StringCcElement.buildStringCcElement(f, args);
	}

	@Override
	protected StringCcElement newFuncAppElement(final StringCcElement f, final StringCcElement arg) {
		return new StringCcElement(f, arg);
	}

//	@Override
//	public StringCcElement getFuncAppElementDetermineIsFunctionYourself(final StringCcElement func,
//			final List<StringCcElement> arguments) {
//		throw new UnsupportedOperationException();
//	}

}

class StringCcElement implements ICongruenceClosureElement<StringCcElement>{

	private final boolean mIsFunctionApplication;
	private final String mName;
	private final StringCcElement mAppliedFunction;
	private final StringCcElement mArgument;
//	private final int mHeight;
	private final Set<StringCcElement> mAfParents;
	private final Set<StringCcElement> mArgParents;

	/**
	 * base element
	 *
	 * @param name
	 * @param isFunction
	 */
	public StringCcElement(final String name) {
		mIsFunctionApplication = false;
		mName = name;
		mAppliedFunction = null;
		mArgument = null;
//		mHeight = 0;
		mAfParents = new HashSet<>();
		mArgParents = new HashSet<>();
	}

	/**
	 * function application
	 *
	 * @param appliedFunction
	 * @param argument
	 * @param isFunction
	 */
	public StringCcElement(final StringCcElement appliedFunction, final StringCcElement argument) {
		mIsFunctionApplication = true;
		mName = null;
		mAppliedFunction = appliedFunction;
//		assert mAppliedFunction.isFunction();
		mArgument = argument;
//		assert !argument.isFunction();
//		mHeight = appliedFunction.getHeight() + 1;
		mAfParents = new HashSet<>();
		mArgParents = new HashSet<>();

	}

	public static StringCcElement buildStringCcElement(final StringCcElement appliedFunction,
			final StringCcElement... arguments) {//, final boolean isFunction) {

		StringCcElement result = appliedFunction;

		for (final StringCcElement arg : arguments) {
			result = new StringCcElement(result, arg);
		}

		return result;
	}

	@Override
	public boolean isFunctionApplication() {
		return mIsFunctionApplication;
	}

	@Override
	public StringCcElement getAppliedFunction() {
		return mAppliedFunction;
	}

	@Override
	public StringCcElement getArgument() {
		return mArgument;
	}

	@Override
	public String toString() {
		if (mIsFunctionApplication) {
			return mAppliedFunction.toString() + "(" + mArgument.toString() + ")";
		} else {
			return mName;
		}
	}

	@Override
	public boolean hasSameTypeAs(final StringCcElement other) {
		return true;
	}

	@Override
	public StringCcElement replaceAppliedFunction(final StringCcElement replacer) {
		throw new UnsupportedOperationException();
	}

	@Override
	public StringCcElement replaceArgument(final StringCcElement replacer) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isLiteral() {
		// TODO Auto-generated method stub
		return false;
	}




//	@Override
//	public StringCcElement[] getArguments() {
//		final StringCcElement[] result = new StringCcElement[mHeight + 1];
//		StringCcElement af = this;
//		for (int i = mHeight; i > 0; i--) {
//			result[i] = af.getArgument();
//			assert !result[i].isFunction();
//			af = af.getAppliedFunction();
//		}
//		result[0] = af.getAppliedFunction();
//		assert result[0].isFunction();
//		return result;
//	}

}
