package de.uni_freiburg.informatik.ultimate.util;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

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
	public void test1() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");
		final StringCCElement g = factory.getFunctionBaseElement("g");

		final StringCCElement x = factory.getNonFunctionBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getNonFunctionFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getNonFunctionFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getNonFunctionBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getNonFunctionFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getNonFunctionFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getNonFunctionBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getNonFunctionFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getNonFunctionFuncAppElement(g, z);
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

		// transitivity
		assertTrue(cc.getEqualityStatus(y, z) == EqualityStatus.EQUAL);

		// congruence (forward)
		assertTrue(cc.getEqualityStatus(f_x, f_y) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_x, f_z) == EqualityStatus.EQUAL);


		assertTrue(cc.getEqualityStatus(f_x, g_x) == EqualityStatus.UNKNOWN);

		cc.reportEquality(f, g);

		assertTrue(cc.getEqualityStatus(f_x, g_x) == EqualityStatus.EQUAL);
	}

	@Test
	public void test2() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");
		final StringCCElement g = factory.getFunctionBaseElement("g");

		final StringCCElement x = factory.getNonFunctionBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getNonFunctionFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getNonFunctionFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getNonFunctionBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getNonFunctionFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getNonFunctionFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getNonFunctionBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getNonFunctionFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getNonFunctionFuncAppElement(g, z);
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
	public void test3() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");
		final StringCCElement g = factory.getFunctionBaseElement("g");

		final StringCCElement x = factory.getNonFunctionBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getNonFunctionFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getNonFunctionFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getNonFunctionBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getNonFunctionFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getNonFunctionFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getNonFunctionBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getNonFunctionFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getNonFunctionFuncAppElement(g, z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		cc.reportDisequality(f_x, f_y);
		assertTrue(cc.getEqualityStatus(f_x, f_y) == EqualityStatus.NOT_EQUAL);
		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.NOT_EQUAL);

	}

	@Test
	public void test4() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");
		final StringCCElement g = factory.getFunctionBaseElement("g");

		final StringCCElement x = factory.getNonFunctionBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getNonFunctionFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getNonFunctionFuncAppElement(g, x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getNonFunctionBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getNonFunctionFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getNonFunctionFuncAppElement(g, y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getNonFunctionBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getNonFunctionFuncAppElement(f, z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getNonFunctionFuncAppElement(g, z);
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
	public void test5() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");

		final StringCCElement x = factory.getNonFunctionBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getNonFunctionFuncAppElement(f, x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement y = factory.getNonFunctionBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getNonFunctionFuncAppElement(f, y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);

		final StringCCElement i = factory.getNonFunctionBaseElement("i");
		cc.getRepresentativeAndAddElementIfNeeded(i);
		final StringCCElement j = factory.getNonFunctionBaseElement("j");
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
	public void test6() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");
		final StringCCElement g = factory.getFunctionBaseElement("g");

		final StringCCElement x1 = factory.getNonFunctionBaseElement("x1");
		cc.getRepresentativeAndAddElementIfNeeded(x1);
		final StringCCElement x2 = factory.getNonFunctionBaseElement("x2");
		cc.getRepresentativeAndAddElementIfNeeded(x2);
		final StringCCElement y1 = factory.getNonFunctionBaseElement("y1");
		cc.getRepresentativeAndAddElementIfNeeded(y1);
		final StringCCElement y2 = factory.getNonFunctionBaseElement("y2");
		cc.getRepresentativeAndAddElementIfNeeded(y2);

		final StringCCElement f_x1_x2 = factory.getNonFunctionFuncAppElement(f, x1, x2);
		cc.getRepresentativeAndAddElementIfNeeded(f_x1_x2);
		final StringCCElement g_y1_y2 = factory.getNonFunctionFuncAppElement(g, y1, y2);
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
	public void test7() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");

		final StringCCElement a = factory.getNonFunctionBaseElement("a");
		final StringCCElement b = factory.getNonFunctionBaseElement("b");
		final StringCCElement f_a = factory.getNonFunctionFuncAppElement(f, a);
		final StringCCElement f_b = factory.getNonFunctionFuncAppElement(f, b);

		cc.reportEquality(a, b);

//		assertTrue(cc.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);

		cc.reportDisequality(f_a, f_b);

		assertTrue(cc.isInconsistent());

	}

	@Test
	public void test7a() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");
		final StringCCElement g = factory.getFunctionBaseElement("g");

		final StringCCElement a = factory.getNonFunctionBaseElement("a");
		final StringCCElement b = factory.getNonFunctionBaseElement("b");
		final StringCCElement f_a_b = factory.getNonFunctionFuncAppElement(f, a, b);
		final StringCCElement g_b_a = factory.getNonFunctionFuncAppElement(g, b, a);

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
	public void test7b() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");
		final StringCCElement g = factory.getFunctionBaseElement("g");

		final StringCCElement a = factory.getNonFunctionBaseElement("a");
		final StringCCElement b = factory.getNonFunctionBaseElement("b");
		final StringCCElement i = factory.getNonFunctionBaseElement("i");
		final StringCCElement j = factory.getNonFunctionBaseElement("j");

		final StringCCElement f_a_i = factory.getNonFunctionFuncAppElement(f, a, i);
		final StringCCElement g_j_b = factory.getNonFunctionFuncAppElement(g, j, b);

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
	public void test8() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");

		final StringCCElement a = factory.getNonFunctionBaseElement("a");
		final StringCCElement b = factory.getNonFunctionBaseElement("b");

		final StringCCElement f_a_b = factory.getNonFunctionFuncAppElement(f, a, b);

		final StringCCElement f_f_a_b_b = factory.getNonFunctionFuncAppElement(f, f_a_b, b);

		cc.reportEquality(f_a_b, a);
		assertFalse(cc.isInconsistent());

		cc.reportDisequality(f_f_a_b_b, a);
		assertTrue(cc.isInconsistent());
	}

	/**
	 * Example from Jochen Hoenicke's Decision Procedures lecture.
	 */
	@Test
	public void test9() {
		final CongruenceClosure<StringCCElement> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");

		final StringCCElement a = factory.getNonFunctionBaseElement("a");
		final StringCCElement f_a = factory.getNonFunctionFuncAppElement(f, a);
		final StringCCElement f2_a = factory.getNonFunctionFuncAppElement(f, f_a);
		final StringCCElement f3_a = factory.getNonFunctionFuncAppElement(f, f2_a);
		final StringCCElement f4_a = factory.getNonFunctionFuncAppElement(f, f3_a);
		final StringCCElement f5_a = factory.getNonFunctionFuncAppElement(f, f4_a);

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
		final CongruenceClosure<StringCCElement> cc1 = new CongruenceClosure<>();
		final CongruenceClosure<StringCCElement> cc2 = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");

		final StringCCElement a = factory.getNonFunctionBaseElement("a");
		final StringCCElement b = factory.getNonFunctionBaseElement("b");

		final StringCCElement i = factory.getNonFunctionBaseElement("i");
		final StringCCElement j = factory.getNonFunctionBaseElement("j");

		final StringCCElement x = factory.getNonFunctionBaseElement("x");
		final StringCCElement y = factory.getNonFunctionBaseElement("y");

		final StringCCElement f_a = factory.getNonFunctionFuncAppElement(f, a);
		final StringCCElement f_f_a = factory.getNonFunctionFuncAppElement(f, f_a);
		final StringCCElement f_b = factory.getNonFunctionFuncAppElement(f, b);
		final StringCCElement f_f_b = factory.getNonFunctionFuncAppElement(f, f_b);


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

		final CongruenceClosure<StringCCElement> cc3 = cc1.join(cc2);
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

		final CongruenceClosure<StringCCElement> cc4 = cc1.meet(cc2);
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
		final CongruenceClosure<StringCCElement> cc1 = new CongruenceClosure<>();
		final CongruenceClosure<StringCCElement> cc2 = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement f = factory.getFunctionBaseElement("f");

		final StringCCElement a = factory.getNonFunctionBaseElement("a");
		final StringCCElement b = factory.getNonFunctionBaseElement("b");

		final StringCCElement i = factory.getNonFunctionBaseElement("i");
		final StringCCElement j = factory.getNonFunctionBaseElement("j");

		final StringCCElement x = factory.getNonFunctionBaseElement("x");
		final StringCCElement y = factory.getNonFunctionBaseElement("y");

		final StringCCElement f_a = factory.getNonFunctionFuncAppElement(f, a);
		final StringCCElement f_f_a = factory.getNonFunctionFuncAppElement(f, f_a);
		final StringCCElement f_b = factory.getNonFunctionFuncAppElement(f, b);
		final StringCCElement f_f_b = factory.getNonFunctionFuncAppElement(f, f_b);


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

		final CongruenceClosure<StringCCElement> cc3 = cc1.join(cc2);
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

		final CongruenceClosure<StringCCElement> cc4 = cc1.meet(cc2);
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



}

class StringElementFactory extends AbstractCCElementFactory<StringCCElement, String> {

	@Override
	protected StringCCElement newBaseElement(final String c, final boolean isFunction) {
		return new StringCCElement(c, isFunction);
	}

	@Override
	protected StringCCElement newFuncAppElement(final StringCCElement f, final List<StringCCElement> args,
			final boolean isFunction) {
		return new StringCCElement(f, args, isFunction);
	}

}

class StringCCElement implements ICongruenceClosureElement<StringCCElement>{

	private final boolean mIsFunctionApplication;
	private final String mName;
	private final StringCCElement mAppliedFunction;
	private final List<StringCCElement> mArguments;
	private final boolean mIsFunction;

	public StringCCElement(final String name) {
		this(name, false);
	}

	public StringCCElement(final String name, final boolean isFunction) {
		mIsFunctionApplication = false;
		mName = name;
		mAppliedFunction = null;
		mArguments = null;
		mIsFunction = isFunction;
	}

	public StringCCElement(final StringCCElement appliedFunction, final List<StringCCElement> arguments) {
		this(appliedFunction, arguments, false);
	}

	public StringCCElement(final StringCCElement appliedFunction, final List<StringCCElement> arguments,
			final boolean isFunction) {
		mIsFunctionApplication = true;
		mName = null;
		mAppliedFunction = appliedFunction;
		assert mAppliedFunction.isFunction();
		mArguments = arguments;
		mIsFunction = isFunction;
	}

	@Override
	public boolean isFunctionApplication() {
		return mIsFunctionApplication;
	}

	@Override
	public StringCCElement getAppliedFunction() {
		return mAppliedFunction;
	}

	@Override
	public List<StringCCElement> getArguments() {
		return mArguments;
	}

	@Override
	public String toString() {
		if (mIsFunctionApplication) {
			return mAppliedFunction.toString() + mArguments.toString();
		} else {
			return mName;
		}
	}

	@Override
	public boolean isFunction() {
		return mIsFunction;
	}

}
