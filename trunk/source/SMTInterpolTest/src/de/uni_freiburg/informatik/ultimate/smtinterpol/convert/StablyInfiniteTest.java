package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.ProofMode;

@RunWith(JUnit4.class)
public class StablyInfiniteTest implements SMTLIBConstants {

	NoopScript mScript;
	Theory mTheory;
	Clausifier mClausifier;
	DataType mList;
	Sort mInt;
	Sort mBool;
	Sort mBitvec;
	Sort mUnit;

	public StablyInfiniteTest() {
		mScript = new NoopScript();
		mScript.setLogic(Logics.ALL);
		mTheory = mScript.getTheory();

		final DPLLEngine dpllEngine = new DPLLEngine(new DefaultLogger(), () -> false);
		mClausifier = new Clausifier(mTheory, dpllEngine, ProofMode.NONE);
		mClausifier.setLogic(Logics.ALL);

		createUnit();
		createList();
		createPair();
		createWrapped();
		createAlt();
		createOption();
		mUnit = mScript.sort("Unit");
		mInt = mScript.sort(INT);
		mBool = mScript.sort(BOOL);
		mBitvec = mScript.sort(BITVEC, new String[] { "4" }, new Sort[0]);
	}

	private DataType createUnit() {
		final DataType unit = mScript.datatype("Unit", 0);
		final DataType.Constructor[] constructors = new DataType.Constructor[] {
				new DataType.Constructor("singleton", new String[0], new Sort[0]) };
		mScript.declareDatatype(unit, constructors);
		return unit;
	}

	private DataType createList() {
		final DataType list = mScript.datatype("List", 1);
		final Sort[] sortParam = mScript.sortVariables("X");
		final DataType.Constructor[] constructors = new DataType.Constructor[] {
				new DataType.Constructor("nil", new String[0], new Sort[0]),
				new DataType.Constructor("cons", new String[] { "car", "cdr" },
						new Sort[] { sortParam[0], mScript.sort("List", sortParam[0]) })
		};
		mScript.declareDatatypes(new DataType[] { list }, new DataType.Constructor[][] { constructors },
				new Sort[][] { sortParam });
		return list;
	}

	private DataType createWrapped() {
		final DataType wrapped = mScript.datatype("Wrapped", 1);
		final Sort[] sortParam = mScript.sortVariables("X");
		final DataType.Constructor[] constructors = new DataType.Constructor[] {
				new DataType.Constructor("wrap", new String[] { "unwrap" }, new Sort[] { sortParam[0] }) };
		mScript.declareDatatypes(new DataType[] { wrapped }, new DataType.Constructor[][] { constructors },
				new Sort[][] { sortParam });
		return wrapped;
	}

	private DataType createPair() {
		final DataType pair = mScript.datatype("Pair", 2);
		final Sort[] sortParam = mScript.sortVariables("X", "Y");
		final DataType.Constructor[] constructors = new DataType.Constructor[] { new DataType.Constructor("pair",
				new String[] { "first", "second" }, new Sort[] { sortParam[0], sortParam[1] }) };
		mScript.declareDatatypes(new DataType[] { pair }, new DataType.Constructor[][] { constructors },
				new Sort[][] { sortParam });
		return pair;
	}

	private DataType createOption() {
		final DataType option = mScript.datatype("Option", 1);
		final Sort[] sortParam = mScript.sortVariables("X");
		final DataType.Constructor[] constructors = new DataType.Constructor[] {
				new DataType.Constructor("null", new String[0], new Sort[0]),
				new DataType.Constructor("option", new String[] { "optval" }, new Sort[] { sortParam[0] }) };
		mScript.declareDatatypes(new DataType[] { option }, new DataType.Constructor[][] { constructors },
				new Sort[][] { sortParam });
		return option;
	}

	private DataType createAlt() {
		final DataType alt = mScript.datatype("Alt", 2);
		final Sort[] sortParam = mScript.sortVariables("X", "Y");
		final DataType.Constructor[] constructors = new DataType.Constructor[] {
				new DataType.Constructor("injLeft", new String[] { "left" }, new Sort[] { sortParam[0] }),
				new DataType.Constructor("injRight", new String[] { "right" }, new Sort[] { sortParam[1] }), };
		mScript.declareDatatypes(new DataType[] { alt }, new DataType.Constructor[][] { constructors },
				new Sort[][] { sortParam });
		return alt;
	}

	@Test
	public void testSingleton() {
		assertTrue(mClausifier.isSingleton(mUnit));
		assertFalse(mClausifier.isSingleton(mScript.sort("List", mUnit)));
		assertFalse(mClausifier.isSingleton(mScript.sort("List", mInt)));
		assertFalse(mClausifier.isSingleton(mScript.sort("Option", mUnit)));
		assertTrue(mClausifier.isSingleton(mScript.sort("Wrapped", mUnit)));
		assertFalse(mClausifier.isSingleton(mScript.sort("Wrapped", mInt)));
		assertFalse(mClausifier.isSingleton(mScript.sort(ARRAY, mUnit, mInt)));
		assertTrue(mClausifier.isSingleton(mScript.sort(ARRAY, mInt, mUnit)));
		assertTrue(mClausifier.isSingleton(mScript.sort("Wrapped", mScript.sort(ARRAY, mInt, mUnit))));
		assertTrue(mClausifier
				.isSingleton(mScript.sort(ARRAY, mInt, mScript.sort("Wrapped", mScript.sort(ARRAY, mInt, mUnit)))));
		assertTrue(mClausifier.isSingleton(mScript.sort("Pair", mUnit, mUnit)));
		assertFalse(mClausifier.isSingleton(mScript.sort("Alt", mUnit, mUnit)));
		assertFalse(mClausifier.isSingleton(mScript.sort("Pair", mInt, mUnit)));
		assertFalse(mClausifier.isSingleton(mScript.sort("Pair", mUnit, mInt)));
	}

	@Test
	public void testSingletonInfinite() {
		assertFalse(mClausifier.isStablyInfinite(mUnit));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("List", mUnit)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("List", mInt)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort("Option", mUnit)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort("Wrapped", mUnit)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("Wrapped", mInt)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mUnit, mInt)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mInt, mUnit)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort("Wrapped", mScript.sort(ARRAY, mInt, mUnit))));
		assertFalse(mClausifier.isStablyInfinite(
				mScript.sort(ARRAY, mInt, mScript.sort("Wrapped", mScript.sort(ARRAY, mInt, mUnit)))));
	}

	@Test
	public void testSimpleInfinite() {
		assertTrue(mClausifier.isStablyInfinite(mInt));
		assertFalse(mClausifier.isStablyInfinite(mBitvec));
		assertFalse(mClausifier.isStablyInfinite(mBool));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mBool, mBool)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mInt, mBool)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mBool, mInt)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mInt, mInt)));
	}

	@Test
	public void testDataInfinite() {
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("List", mUnit)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("Option", mScript.sort("List", mUnit))));
		assertTrue(mClausifier
				.isStablyInfinite(mScript.sort("Pair", mScript.sort("List", mUnit), mScript.sort("List", mUnit))));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("Pair", mUnit, mScript.sort("List", mUnit))));
		assertTrue(mClausifier.isStablyInfinite(
				mScript.sort("Alt", mUnit, mScript.sort("Pair", mUnit, mScript.sort("List", mUnit)))));
		assertTrue(mClausifier
				.isStablyInfinite(mScript.sort(ARRAY, mBool, mScript.sort("Option", mScript.sort("List", mUnit)))));
	}

	@Test
	public void testComplexNoCache() {
		final DPLLEngine dpllEngine = new DPLLEngine(new DefaultLogger(), () -> false);
		mClausifier = new Clausifier(mTheory, dpllEngine, ProofMode.NONE);
		mClausifier.setLogic(Logics.ALL);

		assertTrue(mClausifier
				.isStablyInfinite(mScript.sort("Pair", mScript.sort("List", mUnit),
						mScript.sort("Wrapped", mScript.sort("List", mUnit)))));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("Pair", mUnit, mScript.sort("List", mUnit))));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("List", mUnit)));
	}

	@Test
	public void testNestedUnit() {
		final DataType nestedUnit = mScript.datatype("NestedUnit", 0);
		final DataType.Constructor[] constructors = new DataType.Constructor[] {
				new DataType.Constructor("nest", new String[] { "unnest1", "unnest2" }, new Sort[] { mUnit, mUnit }) };
		mScript.declareDatatype(nestedUnit, constructors);
		assertTrue(mClausifier.isSingleton(mScript.sort("Wrapped", mScript.sort("NestedUnit"))));
	}

	@Test
	public void testRealSort() {
		mScript.defineSort("MyUnit", new Sort[0], mUnit);
		final Sort[] sortParams = mScript.sortVariables("X");
		mScript.defineSort("MyWrapped", sortParams, mScript.sort("Wrapped", sortParams[0]));
		final Sort myUnit = mScript.sort("MyUnit");
		final DataType nestedUnit = mScript.datatype("MyNestedUnit", 0);
		final DataType.Constructor[] constructors = new DataType.Constructor[] {
				new DataType.Constructor("nest", new String[] { "unnest1", "unnest2" }, new Sort[] { myUnit, mUnit }) };
		mScript.declareDatatype(nestedUnit, constructors);

		assertTrue(mClausifier.isSingleton(myUnit));
		assertFalse(mClausifier.isSingleton(mScript.sort("List", myUnit)));
		assertFalse(mClausifier.isSingleton(mScript.sort("List", mInt)));
		assertFalse(mClausifier.isSingleton(mScript.sort("Option", myUnit)));
		assertTrue(mClausifier.isSingleton(mScript.sort("MyWrapped", myUnit)));
		assertFalse(mClausifier.isSingleton(mScript.sort("MyWrapped", mInt)));
		assertTrue(mClausifier.isSingleton(mScript.sort(ARRAY, mInt, myUnit)));
		assertTrue(mClausifier.isSingleton(mScript.sort("Wrapped", mScript.sort("MyNestedUnit"))));

		assertFalse(mClausifier.isStablyInfinite(myUnit));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("List", myUnit)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("List", mInt)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort("Option", myUnit)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort("MyWrapped", myUnit)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort("MyWrapped", mInt)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mInt, myUnit)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mBool, mScript.sort("MyWrapped", mBool))));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mScript.sort("MyWrapped", mBool), mBool)));
		assertTrue(mClausifier.isStablyInfinite(mScript.sort(ARRAY, mScript.sort("MyWrapped", mInt), mBool)));
		assertFalse(mClausifier.isStablyInfinite(mScript.sort("Wrapped", mScript.sort("MyNestedUnit"))));
	}

}
