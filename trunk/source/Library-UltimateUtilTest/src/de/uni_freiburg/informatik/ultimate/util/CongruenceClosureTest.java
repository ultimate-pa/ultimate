package de.uni_freiburg.informatik.ultimate.util;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.AbstractCCElementFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcManager;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosureComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.ICongruenceClosureElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.RemoveCcElement;

public class CongruenceClosureTest {

	// TODO: make it work with this flag set to false, too
	private static final boolean mInPlace = true;

	/**
	 * Test about basic congruence closure operations.
	 */
	@Test
	public void test01() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

		// reflexivity
		assertTrue(cc.getEqualityStatus(x, x) == EqualityStatus.EQUAL);

		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.UNKNOWN);

//		cc.reportEquality(x, z);
		cc = manager.reportEquality(x, z, cc, mInPlace);

		// symmetry
		assertTrue(cc.getEqualityStatus(z, x) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(x, z) == EqualityStatus.EQUAL);

		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.UNKNOWN);

//		cc.reportEquality(x, y);
		cc = manager.reportEquality(x, y, cc, mInPlace);

		assertFalse(cc.isInconsistent());

		// transitivity
		assertTrue(cc.getEqualityStatus(y, z) == EqualityStatus.EQUAL);

		// congruence (forward)
		assertTrue(cc.getEqualityStatus(f_x, f_y) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_x, f_z) == EqualityStatus.EQUAL);


		assertTrue(cc.getEqualityStatus(f_x, g_x) == EqualityStatus.UNKNOWN);

//		cc.reportEquality(f, g);
		cc =manager.reportEquality(f, g, cc, mInPlace);

		assertFalse(cc.isInconsistent());
		assertTrue(cc.getEqualityStatus(f_x, g_x) == EqualityStatus.EQUAL);
	}

	@Test
	public void test02() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

//		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>((ILogger) null);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

//		cc.reportEquality(x, z);
		cc = manager.reportEquality(x, z, cc, mInPlace);

		assertTrue(cc.getEqualityStatus(x, z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(y, z) == EqualityStatus.UNKNOWN);
		assertTrue(cc.getEqualityStatus(f_x, f_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(g_x, g_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_x, g_z) == EqualityStatus.UNKNOWN);

//		cc.reportEquality(f_y, z);
		cc = manager.reportEquality(f_y, z, cc, mInPlace);

		assertTrue(cc.getEqualityStatus(f_y, z) == EqualityStatus.EQUAL);

//		cc.reportEquality(f_x, g_z);
		cc = manager.reportEquality(f_x, g_z, cc, mInPlace);

		assertTrue(cc.getEqualityStatus(f_x, g_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_z, g_x) == EqualityStatus.EQUAL);

//		cc.reportEquality(x, y);
		cc = manager.reportEquality(x, y, cc, mInPlace);

		assertTrue(cc.getEqualityStatus(x, g_z) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(y, f_y) == EqualityStatus.EQUAL);
	}


	@Test
	public void test03() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

		cc = manager.reportDisequality(f_x, f_y, cc, mInPlace);
		assertTrue(cc.getEqualityStatus(f_x, f_y) == EqualityStatus.NOT_EQUAL);
		assertTrue(cc.getEqualityStatus(x, y) == EqualityStatus.NOT_EQUAL);

	}

	@Test
	public void test04() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

//		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>((ILogger) null);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

		cc = manager.reportEquality(f, g, cc, mInPlace);
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
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);

		final StringCcElement i = factory.getBaseElement("i");
		cc = manager.addElement(cc, i, mInPlace, false);
		final StringCcElement j = factory.getBaseElement("j");
		cc = manager.addElement(cc, j, mInPlace, false);

		cc = manager.reportEquality(i, f_y, cc, mInPlace);
		cc = manager.reportDisequality(j, f_x, cc, mInPlace);
		cc = manager.reportEquality(i, j, cc, mInPlace);

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
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

//		final CongruenceClosure<StringCcElement> cc = new CongruenceClosure<>((ILogger) null);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x1 = factory.getBaseElement("x1");
		cc = manager.addElement(cc, x1, mInPlace, false);
		final StringCcElement x2 = factory.getBaseElement("x2");
		cc = manager.addElement(cc, x2, mInPlace, false);
		final StringCcElement y1 = factory.getBaseElement("y1");
		cc = manager.addElement(cc, y1, mInPlace, false);
		final StringCcElement y2 = factory.getBaseElement("y2");
		cc = manager.addElement(cc, y2, mInPlace, false);

		final StringCcElement f_x1_x2 = factory.getFuncAppElement(f, x1, x2);
		cc = manager.addElement(cc, f_x1_x2, mInPlace, false);
		final StringCcElement g_y1_y2 = factory.getFuncAppElement(g, y1, y2);
		cc = manager.addElement(cc, g_y1_y2, mInPlace, false);


		cc = manager.reportDisequality(f_x1_x2, g_y1_y2, cc, mInPlace);
		cc = manager.reportEquality(f, g, cc, mInPlace);

		cc = manager.reportEquality(x1, y1, cc, mInPlace);

		assertTrue(cc.getEqualityStatus(x2, y2) == EqualityStatus.NOT_EQUAL);
	}

	/**
	 * Tests what happens when we don't register all nodes up front (i.e. before the first report*-call).
	 */
	@Test
	public void test07() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement f_a = factory.getFuncAppElement(f, a);
		final StringCcElement f_b = factory.getFuncAppElement(f, b);

		cc = manager.reportEquality(a, b, cc, mInPlace);

//		assertTrue(cc.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);

		cc = manager.reportDisequality(f_a, f_b, cc, mInPlace);

		assertTrue(cc.isInconsistent());

	}

	@Test
	public void test07a() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement f_a_b = factory.getFuncAppElement(f, a, b);
		final StringCcElement g_b_a = factory.getFuncAppElement(g, b, a);

		cc = manager.reportEquality(a, b, cc, mInPlace);

		cc = manager.reportEquality(f, g, cc, mInPlace);

		cc = manager.reportDisequality(f_a_b, g_b_a, cc, mInPlace);

		assertTrue(cc.isInconsistent());

	}

	/**
	 * Test for debugging the congruence propagation done in CongruenceClosure.registerNewElement(..). Checks if the
	 * argument order is accounted for.
	 */
	@Test
	public void test07b() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement i = factory.getBaseElement("i");
		final StringCcElement j = factory.getBaseElement("j");

		final StringCcElement f_a_i = factory.getFuncAppElement(f, a, i);
		final StringCcElement g_j_b = factory.getFuncAppElement(g, j, b);

		cc = manager.reportEquality(a, b, cc, mInPlace);
		cc = manager.reportEquality(i, j, cc, mInPlace);

		cc = manager.reportEquality(f, g, cc, mInPlace);

		/*
		 * At this point we _cannot_ propagate "f(a,i) = g(j,b)" because of argument order. (We could propagate
		 * f(a,i) = g(b,j)..)
		 */
		cc = manager.reportDisequality(f_a_i, g_j_b, cc, mInPlace);

		assertFalse(cc.isInconsistent());
	}


	/**
	 * Example from Jochen Hoenicke's Decision Procedures lecture.
	 *
	 */
	@Test
	public void test08() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");

		final StringCcElement f_a_b = factory.getFuncAppElement(f, a, b);

		final StringCcElement f_f_a_b_b = factory.getFuncAppElement(f, f_a_b, b);

		cc = manager.reportEquality(f_a_b, a, cc, mInPlace);
		assertFalse(cc.isInconsistent());

		cc = manager.reportDisequality(f_f_a_b_b, a, cc, mInPlace);
		assertTrue(cc.isInconsistent());
	}

	/**
	 * Example from Jochen Hoenicke's Decision Procedures lecture.
	 */
	@Test
	public void test09() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement f_a = factory.getFuncAppElement(f, a);
		final StringCcElement f2_a = factory.getFuncAppElement(f, f_a);
		final StringCcElement f3_a = factory.getFuncAppElement(f, f2_a);
		final StringCcElement f4_a = factory.getFuncAppElement(f, f3_a);
		final StringCcElement f5_a = factory.getFuncAppElement(f, f4_a);

		cc = manager.reportEquality(f3_a, a, cc, mInPlace);
		cc = manager.reportEquality(f5_a, a, cc, mInPlace);

		cc = manager.reportDisequality(f_a, a, cc, mInPlace);
		assertTrue(cc.isInconsistent());
	}


	/**
	 * Tests the (quasi-)lattice operations join, meet, isStrongerThan.
	 * Only introduces equalities, no disequalities.
	 */
	@Test
	public void testOperators1() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);



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


		CongruenceClosure<StringCcElement> cc1 = manager.getEmptyCc(mInPlace);
		cc1 = manager.reportEquality(a, b, cc1, mInPlace);
		cc1 = manager.reportEquality(f_f_a, j, cc1, mInPlace);
		cc1 = manager.reportEquality(x, y, cc1, mInPlace);
		cc1 = manager.reportEquality(i, j, cc1, mInPlace);
		cc1 = manager.reportEquality(i, x, cc1, mInPlace);
		cc1 = manager.addElement(cc1, f_f_b, mInPlace, false);
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


		CongruenceClosure<StringCcElement> cc2 = manager.getEmptyCc(mInPlace);
		cc2 = manager.reportEquality(i, x, cc2, mInPlace);
		cc2 = manager.reportEquality(f_a, f_b, cc2, mInPlace);
		cc2 = manager.reportEquality(f_f_a, b, cc2, mInPlace);
		cc2 = manager.reportEquality(f_f_a, a, cc2, mInPlace);
		// state of cc2 should be {{a, b, f(f(a))}, {i,x} {f(a), f(b)}} (the element f_f_b is not known to cc2)
		assertTrue(cc2.getEqualityStatus(a, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(b, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(i, x) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(i, f_a) == EqualityStatus.UNKNOWN);
		assertTrue(cc2.getEqualityStatus(a, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc2.getEqualityStatus(x, f_f_a) == EqualityStatus.UNKNOWN);


		// cc1 and cc2 should be incomparable
		assertFalse(manager.isStrongerThanNoCaching(cc1, cc2));
		assertTrue(!mInPlace || !cc1.isFrozen());
		assertTrue(!mInPlace || !cc2.isFrozen());

		assertFalse(manager.isStrongerThanNoCaching(cc2, cc1));
		assertTrue(!mInPlace || !cc1.isFrozen());
		assertTrue(!mInPlace || !cc2.isFrozen());

//		final CongruenceClosure<StringCcElement> cc3 = manager.join(cc1, cc2, mInPlace);
		final CongruenceClosure<StringCcElement> cc3 = manager.join(
				manager.getCopy(cc1, false),
				manager.getCopy(cc2, false),
				mInPlace);
		assertTrue(!mInPlace || !cc1.isFrozen());
		assertTrue(!mInPlace || !cc2.isFrozen());

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
//		assertTrue(cc1.isStrongerThan(cc3));
		assertTrue(manager.isStrongerThanNoCaching(cc1, cc3));
//		assertFalse(cc3.isStrongerThan(cc1));
		assertFalse(manager.isStrongerThanNoCaching(cc3, cc1));
//		assertTrue(cc2.isStrongerThan(cc3));
		assertTrue(manager.isStrongerThanNoCaching(cc2, cc3));
//		assertFalse(cc3.isStrongerThan(cc2));
		assertFalse(manager.isStrongerThanNoCaching(cc3, cc2));
		assertTrue(!mInPlace || !cc1.isFrozen());
		assertTrue(!mInPlace || !cc2.isFrozen());

		final CongruenceClosure<StringCcElement> cc4 = manager.meet(
				manager.getCopy(cc1, true),
				manager.getCopy(cc2, false),
				mInPlace);
		// state of cc4 should be {{a, b, i, j, x, y, f(f(a)), f(f(b))}, {f(a), f(b)}}
		assertTrue(cc4.getEqualityStatus(a, b) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(b, i) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(i, j) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(x, y) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(y, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(f_f_b, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(f_b, f_a) == EqualityStatus.EQUAL);
		assertTrue(cc4.getEqualityStatus(b, f_b) == EqualityStatus.UNKNOWN);

		// cc4 should be strictly stronger than both cc1 and cc2
//		assertTrue(cc4.isStrongerThan(cc1));
		assertTrue(manager.isStrongerThanNoCaching(cc4, cc1));
//		assertFalse(cc1.isStrongerThan(cc4));
		assertFalse(manager.isStrongerThanNoCaching(cc1, cc4));
//		assertTrue(cc4.isStrongerThan(cc2));
		assertTrue(manager.isStrongerThanNoCaching(cc4, cc2));
//		assertFalse(cc2.isStrongerThan(cc4));
		assertFalse(manager.isStrongerThanNoCaching(cc2, cc4));
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
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);


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


		CongruenceClosure<StringCcElement> cc1 = manager.getEmptyCc(mInPlace);
		cc1 = manager.reportEquality(a, b, cc1, mInPlace);
		cc1 = manager.reportEquality(f_f_a, j, cc1, mInPlace);
		cc1 = manager.reportEquality(x, y, cc1, mInPlace);
		cc1 = manager.reportEquality(i, j, cc1, mInPlace);
		cc1 = manager.reportEquality(i, x, cc1, mInPlace);
		cc1 = manager.addElement(cc1, f_f_b, mInPlace, false);
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

		CongruenceClosure<StringCcElement> cc2 = manager.getEmptyCc(mInPlace);
		cc2 = manager.reportEquality(i, x, cc2, mInPlace);
		cc2 = manager.reportEquality(f_a, f_b, cc2, mInPlace);
		cc2 = manager.reportEquality(f_f_a, b, cc2, mInPlace);
		cc2 = manager.reportEquality(f_f_a, a, cc2, mInPlace);
		cc2 = manager.reportDisequality(f_b, x, cc2, mInPlace);
		// ONLY CHANGE to testOperators1 in terms of constraints in cc1 and cc2
		// state of cc2 should be {{a, b, f(f(a))}, {i,x} {f(a), f(b)}}, x != f(a) (element f_f_b is not known to cc2)
		assertTrue(cc2.getEqualityStatus(a, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(b, f_f_a) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(i, x) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc2.getEqualityStatus(x, f_a) == EqualityStatus.NOT_EQUAL);
		assertTrue(cc2.getEqualityStatus(a, i) == EqualityStatus.UNKNOWN);
		assertTrue(cc2.getEqualityStatus(x, f_f_a) == EqualityStatus.UNKNOWN);


		// cc1 and cc2 should be incomparable
		assertFalse(manager.isStrongerThanNoCaching(cc1, cc2));
		assertFalse(manager.isStrongerThanNoCaching(cc2, cc1));

		final CongruenceClosure<StringCcElement> cc3 = manager.join(
				manager.getCopy(cc1, true),
				manager.getCopy(cc2, true),
				mInPlace);
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
		assertTrue(manager.isStrongerThanNoCaching(cc1, cc3));
		assertFalse(manager.isStrongerThanNoCaching(cc3, cc1));
		assertTrue(manager.isStrongerThanNoCaching(cc2, cc3));
		assertFalse(manager.isStrongerThanNoCaching(cc3, cc2));

		final CongruenceClosure<StringCcElement> cc4 = manager.meet(
				manager.getCopy(cc1, true),
				manager.getCopy(cc2, true),
				mInPlace);
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
		assertTrue(manager.isStrongerThanNoCaching(cc4, cc1));
		assertFalse(manager.isStrongerThanNoCaching(cc1, cc4));
		assertTrue(manager.isStrongerThanNoCaching(cc4, cc2));
		assertFalse(manager.isStrongerThanNoCaching(cc2, cc4));

	}

		/**
	 * test to check how the join operator cooperates with the literals-feature of CongruenceClosure.
	 * (expressions can be marked as literals, and all literals are implicitly pairwise distinct)
	 */
	@Test
	public void testOperators3() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);


		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement x = factory.getBaseElement("x");
		// get zero, one as literals
		final StringCcElement zero = factory.getBaseElement("0", true);
		final StringCcElement one = factory.getBaseElement("1", true);

		// "x = 0"
		final CongruenceClosure<StringCcElement> cc1 = manager.getSingleEqualityCc(x, zero, false);
//		assertTrue(cc1.getEqualityStatus(x, one) == EqualityStatus.NOT_EQUAL);

		// "x != 1"
		final CongruenceClosure<StringCcElement> cc2 = manager.getSingleDisequalityCc(x, one, false);

		// expected join: x != 1 (because x = 0 implies that x != 1)
		final CongruenceClosure<StringCcElement> join = manager.join(cc1, cc2, false);
		assertTrue(join.getEqualityStatus(x, one) == EqualityStatus.NOT_EQUAL);

	}

	/**
	 * We store disequalities only over representatives. Because the join operator may 'split' representatives, we
	 *  may have to 'split' disequalities during join.
	 * This test checks checks part of that functionality.
	 *
	 *  c1: {x, y}, a != x
     *  c2: {x}, {y}, a != x, a != y
     *  c1 join c2: {x}, {y}, a != x, a != y
	 *
	 */
	@Test
	public void testOperators4() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);


		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement x = factory.getBaseElement("x");
		final StringCcElement y = factory.getBaseElement("y");
		final StringCcElement a = factory.getBaseElement("a");

		CongruenceClosure<StringCcElement> cc1 = manager.getEmptyCc(mInPlace);
		cc1 = manager.reportEquality(x, y, cc1, mInPlace);
		cc1 = manager.reportDisequality(a, x, cc1, mInPlace);

		CongruenceClosure<StringCcElement> cc2 = manager.getEmptyCc(mInPlace);
		cc2 = manager.reportDisequality(a, x, cc1, mInPlace);
		cc2 = manager.reportDisequality(a, y, cc1, mInPlace);

		final CongruenceClosure<StringCcElement> join = manager.join(cc1, cc2, mInPlace);


		assertTrue(manager.isStrongerThan(cc2, join));
		assertTrue(manager.isStrongerThan(join, cc2));
	}




	@Test
	public void testRemove01() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement c = factory.getBaseElement("c");

		cc = manager.reportEquality(a, b, cc, mInPlace);
		cc = manager.reportEquality(b, c, cc, mInPlace);
		assertTrue(cc.getEqualityStatus(a, c) == EqualityStatus.EQUAL);
		RemoveCcElement.removeSimpleElement(cc, b);
		assertTrue(cc.getEqualityStatus(a, c) == EqualityStatus.EQUAL);
		cc = manager.addElement(cc, b, mInPlace, false);
		assertTrue(cc.getEqualityStatus(a, b) == EqualityStatus.UNKNOWN);
	}

	@Test
	public void testRemove02() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement c = factory.getBaseElement("c");

		final StringCcElement f_a = factory.getOrConstructFuncAppElement(f, a);
		final StringCcElement f_b = factory.getOrConstructFuncAppElement(f, b);
		final StringCcElement f_c = factory.getOrConstructFuncAppElement(f, c);

		cc = manager.reportEquality(a, b, cc, mInPlace);
		cc = manager.reportEquality(b, c, cc, mInPlace);
		cc = manager.addElement(cc, f_a, mInPlace, false);
		cc = manager.addElement(cc, f_b, mInPlace, false);
		cc = manager.addElement(cc, f_c, mInPlace, false);
		assertTrue(cc.getEqualityStatus(f_a, f_b) == EqualityStatus.EQUAL);
		assertTrue(cc.getEqualityStatus(f_c, f_b) == EqualityStatus.EQUAL);
		RemoveCcElement.removeSimpleElement(cc, b);
		assertTrue(cc.getEqualityStatus(f_a, f_c) == EqualityStatus.EQUAL);
		cc = manager.addElement(cc, f_b, mInPlace, false);
		assertTrue(cc.getEqualityStatus(f_a, f_b) == EqualityStatus.UNKNOWN);
	}

	@Test
	public void testRemove03() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement a = factory.getBaseElement("a");
		final StringCcElement b = factory.getBaseElement("b");
		final StringCcElement c = factory.getBaseElement("c");

		final StringCcElement f_a = factory.getOrConstructFuncAppElement(f, a);
		final StringCcElement f_b = factory.getOrConstructFuncAppElement(f, b);
		final StringCcElement f_c = factory.getOrConstructFuncAppElement(f, c);

		cc = manager.reportEquality(a, b, cc, mInPlace);
		cc = manager.reportEquality(b, c, cc, mInPlace);
		cc = manager.addElement(cc, f_a, mInPlace, false);
		cc = manager.addElement(cc, f_c, mInPlace, false);
		assertTrue(cc.getEqualityStatus(f_a, f_c) == EqualityStatus.EQUAL);
		RemoveCcElement.removeSimpleElement(cc, a);
		cc = manager.addElement(cc, f_b, mInPlace, false);
		assertTrue(cc.getEqualityStatus(f_b, f_c) == EqualityStatus.EQUAL);
	}

	@Test
	public void testRemove04() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement a = factory.getBaseElement("a");

		final StringCcElement x = factory.getBaseElement("x");
		final StringCcElement y = factory.getBaseElement("y");
		final StringCcElement i = factory.getBaseElement("i");

		final StringCcElement l1 = factory.getBaseElement("1");

		final StringCcElement a_x = factory.getOrConstructFuncAppElement(a, x);
		final StringCcElement a_y = factory.getOrConstructFuncAppElement(a, y);

		cc = manager.reportEquality(a_y, l1, cc, mInPlace);
		cc = manager.reportEquality(i, y, cc, mInPlace);
		RemoveCcElement.removeSimpleElement(cc, y);
		cc = manager.reportEquality(x, i, cc, mInPlace);
		cc = manager.addElement(cc, a_x, mInPlace, false);
		assertTrue(cc.getEqualityStatus(a_x, l1) == EqualityStatus.EQUAL);
	}

	@Test
	public void testContainsConstraints01() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

		// create some literals
		final StringCcElement l1 = factory.getBaseElement("l1", true);
		cc = manager.addElement(cc, l1, mInPlace, false);
		final StringCcElement l2 = factory.getBaseElement("l2", true);
		cc = manager.addElement(cc, l2, mInPlace, false);
		final StringCcElement l3 = factory.getBaseElement("l3", true);
		cc = manager.addElement(cc, l3, mInPlace, false);

		final Set<StringCcElement> l1AndL2 = new HashSet<>();
		{
			l1AndL2.add(l1);
			l1AndL2.add(l2);
		}

		cc = manager.reportContainsConstraint(x, l1AndL2, cc, mInPlace);

		assertTrue(cc.getEqualityStatus(x, l3) == EqualityStatus.NOT_EQUAL);
	}

	/**
	 * In this test case, set constraints with non-literals occur, but they can directly be expanded to literals.
	 */
	@Test
	public void testContainsConstraints02() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

		// create some literals
		final StringCcElement l1 = factory.getBaseElement("l1", true);
		cc = manager.addElement(cc, l1, mInPlace, false);
		final StringCcElement l2 = factory.getBaseElement("l2", true);
		cc = manager.addElement(cc, l2, mInPlace, false);
		final StringCcElement l3 = factory.getBaseElement("l3", true);
		cc = manager.addElement(cc, l3, mInPlace, false);
		final StringCcElement l4 = factory.getBaseElement("l4", true);
		cc = manager.addElement(cc, l4, mInPlace, false);

		final Set<StringCcElement> l1AndL2 = new HashSet<>();
		{
			l1AndL2.add(l1);
			l1AndL2.add(l2);
		}

		cc = manager.reportContainsConstraint(x, l1AndL2, cc, mInPlace);

		final Set<StringCcElement> l3AndX = new HashSet<>();
		{
			l3AndX.add(l3);
			l3AndX.add(x);
		}

		// report y in { l3, x }
		cc = manager.reportContainsConstraint(y, l3AndX, cc, mInPlace);
//		cc = manager.reportContainsConstraint(y, Collections.singleton(l3), cc, mInPlace);

		// y in { l1, l2, l3 } should hold now

		assertTrue(cc.getEqualityStatus(y, l4) == EqualityStatus.NOT_EQUAL);
	}

	/**
	 * This test is about the extension of the contains constraint domain with non-literal elements in set-constraints.
	 * Here, the non-literals cannot directly be expanded to literals.
	 *
	 */
	@Test
	public void testContainsConstraints03() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

		// create some literals
		final StringCcElement l1 = factory.getBaseElement("l1", true);
		cc = manager.addElement(cc, l1, mInPlace, false);
		final StringCcElement l2 = factory.getBaseElement("l2", true);
		cc = manager.addElement(cc, l2, mInPlace, false);
		final StringCcElement l3 = factory.getBaseElement("l3", true);
		cc = manager.addElement(cc, l3, mInPlace, false);
		final StringCcElement l4 = factory.getBaseElement("l4", true);
		cc = manager.addElement(cc, l4, mInPlace, false);


		final Set<StringCcElement> l3AndX = new HashSet<>();
		{
			l3AndX.add(l3);
			l3AndX.add(x);
		}

		// report y in { l3, x }
		cc = manager.reportContainsConstraint(y, l3AndX, cc, mInPlace);

		final Set<StringCcElement> l1AndL2 = new HashSet<>();
		{
			l1AndL2.add(l1);
			l1AndL2.add(l2);
		}

		// report x in { l1, l2 }
		cc = manager.reportContainsConstraint(x, l1AndL2, cc, mInPlace);


		// y in { l1, l2, l3 } should hold now

		assertTrue(cc.getEqualityStatus(y, l4) == EqualityStatus.NOT_EQUAL);
	}

	@Test
	public void testContainsConstraints04() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc = manager.addElement(cc, x, mInPlace, false);
		final StringCcElement f_x = factory.getFuncAppElement(f, x);
		cc = manager.addElement(cc, f_x, mInPlace, false);
		final StringCcElement g_x = factory.getFuncAppElement(g, x);
		cc = manager.addElement(cc, g_x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc = manager.addElement(cc, y, mInPlace, false);
		final StringCcElement f_y = factory.getFuncAppElement(f, y);
		cc = manager.addElement(cc, f_y, mInPlace, false);
		final StringCcElement g_y = factory.getFuncAppElement(g, y);
		cc = manager.addElement(cc, g_y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc = manager.addElement(cc, z, mInPlace, false);
		final StringCcElement f_z = factory.getFuncAppElement(f, z);
		cc = manager.addElement(cc, f_z, mInPlace, false);
		final StringCcElement g_z = factory.getFuncAppElement(g, z);
		cc = manager.addElement(cc, g_z, mInPlace, false);

		// create some literals
		final StringCcElement l1 = factory.getBaseElement("l1", true);
		cc = manager.addElement(cc, l1, mInPlace, false);
		final StringCcElement l2 = factory.getBaseElement("l2", true);
		cc = manager.addElement(cc, l2, mInPlace, false);
		final StringCcElement l3 = factory.getBaseElement("l3", true);
		cc = manager.addElement(cc, l3, mInPlace, false);
		final StringCcElement l4 = factory.getBaseElement("l4", true);
		cc = manager.addElement(cc, l4, mInPlace, false);


		final Set<StringCcElement> l3AndX = new HashSet<>();
		{
			l3AndX.add(l3);
			l3AndX.add(x);
		}

		// report y in { l3, x }
		cc = manager.reportContainsConstraint(y, l3AndX, cc, mInPlace);

		final Set<StringCcElement> l1AndL2 = new HashSet<>();
		{
			l1AndL2.add(l1);
			l1AndL2.add(l2);
		}

		// report x ~ l1
		cc = manager.reportEquality(x, l1, cc, mInPlace);


		// y in { l1, l2, l3 } should hold now

		assertTrue(cc.getEqualityStatus(y, l4) == EqualityStatus.NOT_EQUAL);
	}

	/**
	 * We store set constraints only over representatives. Because the join operator may 'split' representatives, we
	 *  may have to 'split' set constraints during join.
	 * This test checks checks part of that functionality.
	 */
	@Test
	public void testContainsConstraints05() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc1 = manager.getEmptyCc(mInPlace);
		CongruenceClosure<StringCcElement> cc2 = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement f = factory.getBaseElement("f");
		final StringCcElement g = factory.getBaseElement("g");

		final StringCcElement x = factory.getBaseElement("x");
		cc1 = manager.addElement(cc1, x, mInPlace, false);
		cc2 = manager.addElement(cc2, x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc1 = manager.addElement(cc1, y, mInPlace, false);
		cc2 = manager.addElement(cc2, y, mInPlace, false);

		final StringCcElement z = factory.getBaseElement("z");
		cc1 = manager.addElement(cc1, z, mInPlace, false);
		cc2 = manager.addElement(cc2, z, mInPlace, false);

		final StringCcElement a = factory.getBaseElement("a");
		cc1 = manager.addElement(cc1, a, mInPlace, false);
		cc2 = manager.addElement(cc2, a, mInPlace, false);

		final StringCcElement b = factory.getBaseElement("b");
		cc1 = manager.addElement(cc1, b, mInPlace, false);
		cc2 = manager.addElement(cc2, b, mInPlace, false);

		cc1 = manager.reportEquality(x, y, cc1, mInPlace);
		cc1 = manager.reportEquality(y, z, cc1, mInPlace);

		CongruenceClosure<StringCcElement> cc4 = manager.copyNoRemInfo(cc1);
		cc4 = manager.reportContainsConstraint(x, new HashSet<>(Arrays.asList(new StringCcElement[] { a, b })), cc4,
				mInPlace);
		// cc4 = {x, y, z}, {a}, {b}, x in {a, b}

		cc1 = manager.reportEquality(z, a, cc1, mInPlace);
		// cc1 = {x, y, z, a}, {b}

		cc2 = manager.reportEquality(x, y, cc2, mInPlace);
		cc2 = manager.reportEquality(y, z, cc2, mInPlace);
		cc2 = manager.reportEquality(z, b, cc2, mInPlace);
		// cc2 = {x, y, z, b}, {a}

		final CongruenceClosure<StringCcElement> cc3 = manager.join(cc1, cc2, mInPlace);
		// cc3 should be {x, y, z}, {a}, {b}, x in {a, b}


		// cc3 and cc4 should be equivalent
		assertTrue(manager.isStrongerThan(cc3, cc4));;
		assertTrue(manager.isStrongerThan(cc4, cc3));;
	}




	/**
	 * We store set constraints only over representatives. Because the join operator may 'split' representatives, we
	 *  may have to 'split' set constraints during join.
	 * This test checks checks part of that functionality.
	 */
	@Test
	public void testContainsConstraints06() {
		final ILogger logger = new ConsoleLogger();
		final CongruenceClosureComparator<StringCcElement> ccComparator =
				new CongruenceClosureComparator<StringCcElement>();
		final CcManager<StringCcElement> manager = new CcManager<>(logger, ccComparator);

		CongruenceClosure<StringCcElement> cc1 = manager.getEmptyCc(mInPlace);
		CongruenceClosure<StringCcElement> cc2 = manager.getEmptyCc(mInPlace);
		CongruenceClosure<StringCcElement> cc4 = manager.getEmptyCc(mInPlace);

		final StringElementFactory factory = new StringElementFactory();

		final StringCcElement x = factory.getBaseElement("x");
		cc1 = manager.addElement(cc1, x, mInPlace, false);
		cc2 = manager.addElement(cc2, x, mInPlace, false);
		cc4 = manager.addElement(cc4, x, mInPlace, false);

		final StringCcElement y = factory.getBaseElement("y");
		cc1 = manager.addElement(cc1, y, mInPlace, false);
		cc2 = manager.addElement(cc2, y, mInPlace, false);
		cc4 = manager.addElement(cc4, y, mInPlace, false);

		final StringCcElement a = factory.getBaseElement("a");
		cc1 = manager.addElement(cc1, a, mInPlace, false);
		cc2 = manager.addElement(cc2, a, mInPlace, false);
		cc4 = manager.addElement(cc4, a, mInPlace, false);

		final StringCcElement b = factory.getBaseElement("b");
		cc1 = manager.addElement(cc1, b, mInPlace, false);
		cc2 = manager.addElement(cc2, b, mInPlace, false);
		cc4 = manager.addElement(cc4, b, mInPlace, false);


		cc1 = manager.reportEquality(x, y, cc1, mInPlace);
		cc1 = manager.reportContainsConstraint(a, new HashSet<>(Arrays.asList(new StringCcElement[] { x, b })), cc1,
				mInPlace);
		// cc1 = {x, y}, a in {x, b}

		cc2 = manager.reportContainsConstraint(a, new HashSet<>(Arrays.asList(new StringCcElement[] { x, b })), cc2,
				mInPlace);
		cc2 = manager.reportContainsConstraint(a, new HashSet<>(Arrays.asList(new StringCcElement[] { y, b })), cc2,
				mInPlace);
		// cc2 = {x},{y}, a in {x, b}, a in {y, b}

		final CongruenceClosure<StringCcElement> cc3 = manager.join(cc1, cc2, mInPlace);
		// cc3 should be {x}, {y}, a in {x, b}, a in {y, b} (= cc2, not nice, but should be ok..)


		cc4 = manager.reportContainsConstraint(a, new HashSet<>(Arrays.asList(new StringCcElement[] { x, b })), cc4,
				mInPlace);
		cc4 = manager.reportContainsConstraint(a, new HashSet<>(Arrays.asList(new StringCcElement[] { y, b })), cc4,
				mInPlace);
		// cc4 = {x}, {y}, a in {x, b}, a in {y, b}

		// cc3 and cc4 should be equivalent
		assertTrue(manager.isStrongerThan(cc3, cc4));;
		assertTrue(manager.isStrongerThan(cc4, cc3));;
	}


	// TODO test transformer

}

class StringElementFactory extends AbstractCCElementFactory<StringCcElement, String> {

	@Override
	protected StringCcElement newBaseElement(final String c, final boolean isLiteral) {
		return new StringCcElement(c, isLiteral);
	}

//	protected StringCcElement newLiteral(final String c) {
//		return new StringCcElement(c, true);
//	}

	public StringCcElement getFuncAppElement(final StringCcElement f, final StringCcElement... args) {
		return StringCcElement.buildStringCcElement(this, f, args);
	}

	@Override
	protected StringCcElement newFuncAppElement(final StringCcElement f, final StringCcElement arg) {
		return new StringCcElement(f, arg, this);
	}
}

class StringCcElement implements ICongruenceClosureElement<StringCcElement>{

	private final boolean mIsFunctionApplication;
	private final String mName;
	private final StringCcElement mAppliedFunction;
	private final StringCcElement mArgument;
	private final Set<StringCcElement> mAfParents;
	private final Set<StringCcElement> mArgParents;
	private final StringElementFactory mFactory;
	private final boolean mIsLiteral;

	/**
	 * base element
	 *
	 * @param name
	 * @param isFunction
	 */
	public StringCcElement(final String name, final boolean isLiteral) {
		mIsFunctionApplication = false;
		mName = name;
		mAppliedFunction = null;
		mArgument = null;
		mAfParents = new HashSet<>();
		mArgParents = new HashSet<>();
		mFactory = null;
		mIsLiteral = isLiteral;
	}

	/**
	 * function application
	 *
	 * @param appliedFunction
	 * @param argument
	 * @param isFunction
	 */
	public StringCcElement(final StringCcElement appliedFunction, final StringCcElement argument,
			final StringElementFactory factory) {
		mIsFunctionApplication = true;
		mName = null;
		mAppliedFunction = appliedFunction;
		mArgument = argument;
		mAfParents = new HashSet<>();
		mArgParents = new HashSet<>();
		mFactory = factory;
		mIsLiteral = false;
	}

	public static StringCcElement buildStringCcElement(final StringElementFactory factory,
			final StringCcElement appliedFunction, final StringCcElement... arguments) {//, final boolean isFunction) {

		StringCcElement result = appliedFunction;

		for (final StringCcElement arg : arguments) {
			result = new StringCcElement(result, arg, factory);
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
		return mFactory.getOrConstructFuncAppElement(replacer, mArgument);
	}

	@Override
	public StringCcElement replaceArgument(final StringCcElement replacer) {
		return mFactory.getOrConstructFuncAppElement(mAppliedFunction, replacer);
	}

	@Override
	public boolean isLiteral() {
		return mIsLiteral;
	}

	@Override
	public StringCcElement replaceSubNode(final Map<StringCcElement, StringCcElement> replacementMapping) {
		throw new UnsupportedOperationException("implement this if needed");
	}

	@Override
	public boolean isDependentNonFunctionApplication() {
		// TODO edit when we need dependent nodes here
		return false;
	}

	@Override
	public Set<StringCcElement> getSupportingNodes() {
		throw new UnsupportedOperationException("implement this if needed");
	}
}
