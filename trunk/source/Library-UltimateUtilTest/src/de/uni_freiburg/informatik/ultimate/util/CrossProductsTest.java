package de.uni_freiburg.informatik.ultimate.util;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Collection;
import java.util.HashSet;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class CrossProductsTest {

	@Test
	public void binarySelectiveCrossProductTest1() {

		final Collection<String> set = new HashSet<>();
		set.add("a");
		set.add("b");
		set.add("c");

		final boolean returnReflexivePairs = true;
		final boolean returnSymmetricPairs = true;

		final HashRelation<String, String> crossProduct =
				CrossProducts.binarySelectiveCrossProduct(set, returnReflexivePairs, returnSymmetricPairs);

		assertTrue(crossProduct.containsPair("a", "a"));
		assertTrue(crossProduct.containsPair("a", "b"));
		assertTrue(crossProduct.containsPair("a", "c"));

		assertTrue(crossProduct.containsPair("b", "a"));
		assertTrue(crossProduct.containsPair("b", "b"));
		assertTrue(crossProduct.containsPair("b", "c"));

		assertTrue(crossProduct.containsPair("c", "a"));
		assertTrue(crossProduct.containsPair("c", "b"));
		assertTrue(crossProduct.containsPair("c", "c"));

		assertFalse(crossProduct.containsPair("a", "d"));

	}

	@Test
	public void binarySelectiveCrossProductTest2() {

		final Collection<String> set = new HashSet<>();
		set.add("a");
		set.add("b");
		set.add("c");

		final boolean returnReflexivePairs = false;
		final boolean returnSymmetricPairs = true;

		final HashRelation<String, String> crossProduct =
				CrossProducts.binarySelectiveCrossProduct(set, returnReflexivePairs, returnSymmetricPairs);

		assertFalse(crossProduct.containsPair("a", "a"));
		assertTrue(crossProduct.containsPair("a", "b"));
		assertTrue(crossProduct.containsPair("a", "c"));

		assertTrue(crossProduct.containsPair("b", "a"));
		assertFalse(crossProduct.containsPair("b", "b"));
		assertTrue(crossProduct.containsPair("b", "c"));

		assertTrue(crossProduct.containsPair("c", "a"));
		assertTrue(crossProduct.containsPair("c", "b"));
		assertFalse(crossProduct.containsPair("c", "c"));

		assertFalse(crossProduct.containsPair("a", "d"));

	}

	@Test
	public void binarySelectiveCrossProductTest3() {

		final Collection<String> set = new HashSet<>();
		set.add("a");
		set.add("b");
		set.add("c");

		final boolean returnReflexivePairs = true;
		final boolean returnSymmetricPairs = false;

		final HashRelation<String, String> crossProduct =
				CrossProducts.binarySelectiveCrossProduct(set, returnReflexivePairs, returnSymmetricPairs);

		assertTrue(crossProduct.containsPair("a", "a"));
		assertTrue((crossProduct.containsPair("a", "b") && !crossProduct.containsPair("b", "a"))
				|| (!crossProduct.containsPair("a", "b") && crossProduct.containsPair("b", "a")));
		assertTrue((crossProduct.containsPair("a", "c") && !crossProduct.containsPair("c", "a"))
				|| (!crossProduct.containsPair("a", "c") && crossProduct.containsPair("c", "a")));

		assertTrue(crossProduct.containsPair("b", "b"));
		assertTrue((crossProduct.containsPair("a", "b") && !crossProduct.containsPair("b", "a"))
				|| (!crossProduct.containsPair("a", "b") && crossProduct.containsPair("b", "a")));
		assertTrue((crossProduct.containsPair("b", "c") && !crossProduct.containsPair("c", "b"))
				|| (!crossProduct.containsPair("b", "c") && crossProduct.containsPair("c", "b")));

		assertTrue(crossProduct.containsPair("c", "c"));
		assertTrue((crossProduct.containsPair("c", "b") && !crossProduct.containsPair("b", "c"))
				|| (!crossProduct.containsPair("c", "b") && crossProduct.containsPair("b", "c")));
		assertTrue((crossProduct.containsPair("a", "c") && !crossProduct.containsPair("c", "a"))
				|| (!crossProduct.containsPair("a", "c") && crossProduct.containsPair("c", "a")));

		assertFalse(crossProduct.containsPair("a", "d"));
		assertFalse(crossProduct.containsPair("d", "a"));
		assertFalse(crossProduct.containsPair("d", "d"));

	}

	@Test
	public void binarySelectiveCrossProductTest4() {

		final Collection<String> set = new HashSet<>();
		set.add("a");
		set.add("b");
		set.add("c");

		final boolean returnReflexivePairs = false;
		final boolean returnSymmetricPairs = false;

		final HashRelation<String, String> crossProduct =
				CrossProducts.binarySelectiveCrossProduct(set, returnReflexivePairs, returnSymmetricPairs);

		assertFalse(crossProduct.containsPair("a", "a"));
		assertTrue((crossProduct.containsPair("a", "b") && !crossProduct.containsPair("b", "a"))
				|| (!crossProduct.containsPair("a", "b") && crossProduct.containsPair("b", "a")));
		assertTrue((crossProduct.containsPair("a", "c") && !crossProduct.containsPair("c", "a"))
				|| (!crossProduct.containsPair("a", "c") && crossProduct.containsPair("c", "a")));

		assertFalse(crossProduct.containsPair("b", "b"));
		assertTrue((crossProduct.containsPair("a", "b") && !crossProduct.containsPair("b", "a"))
				|| (!crossProduct.containsPair("a", "b") && crossProduct.containsPair("b", "a")));
		assertTrue((crossProduct.containsPair("b", "c") && !crossProduct.containsPair("c", "b"))
				|| (!crossProduct.containsPair("b", "c") && crossProduct.containsPair("c", "b")));

		assertFalse(crossProduct.containsPair("c", "c"));
		assertTrue((crossProduct.containsPair("c", "b") && !crossProduct.containsPair("b", "c"))
				|| (!crossProduct.containsPair("c", "b") && crossProduct.containsPair("b", "c")));
		assertTrue((crossProduct.containsPair("a", "c") && !crossProduct.containsPair("c", "a"))
				|| (!crossProduct.containsPair("a", "c") && crossProduct.containsPair("c", "a")));

		assertFalse(crossProduct.containsPair("a", "d"));
		assertFalse(crossProduct.containsPair("d", "a"));
		assertFalse(crossProduct.containsPair("d", "d"));

	}
}
