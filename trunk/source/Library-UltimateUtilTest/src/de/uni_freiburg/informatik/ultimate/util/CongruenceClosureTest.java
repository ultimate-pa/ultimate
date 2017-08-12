package de.uni_freiburg.informatik.ultimate.util;

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Equality;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class CongruenceClosureTest {

	/**
	 * Test about basic congruence closure operations.
	 */
	@Test
	public void test1() {
		final CongruenceClosure<StringCCElement, String> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getFuncAppElement("f", x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getFuncAppElement("g", x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getFuncAppElement("f", y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getFuncAppElement("g", y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getFuncAppElement("f", z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getFuncAppElement("g", z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		// reflexivity
		assertTrue(cc.getEqualityStatus(x, x) == Equality.EQUAL);

		assertTrue(cc.getEqualityStatus(x, y) == Equality.UNKNOWN);

		cc.reportEquality(x, z);

		// symmetry
		assertTrue(cc.getEqualityStatus(z, x) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(x, z) == Equality.EQUAL);

		assertTrue(cc.getEqualityStatus(x, y) == Equality.UNKNOWN);

		cc.reportEquality(x, y);

		// transitivity
		assertTrue(cc.getEqualityStatus(y, z) == Equality.EQUAL);

		// congruence (forward)
		assertTrue(cc.getEqualityStatus(f_x, f_y) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(f_x, f_z) == Equality.EQUAL);


		assertTrue(cc.getEqualityStatus(f_x, g_x) == Equality.UNKNOWN);

		cc.reportFunctionEquality("f", "g");

		assertTrue(cc.getEqualityStatus(f_x, g_x) == Equality.EQUAL);
	}

	@Test
	public void test2() {
		final CongruenceClosure<StringCCElement, String> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getFuncAppElement("f", x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getFuncAppElement("g", x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getFuncAppElement("f", y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getFuncAppElement("g", y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getFuncAppElement("f", z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getFuncAppElement("g", z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		cc.reportEquality(x, z);

		assertTrue(cc.getEqualityStatus(x, z) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(y, z) == Equality.UNKNOWN);
		assertTrue(cc.getEqualityStatus(f_x, f_z) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(g_x, g_z) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(f_x, g_z) == Equality.UNKNOWN);

		cc.reportEquality(f_y, z);

		assertTrue(cc.getEqualityStatus(f_y, z) == Equality.EQUAL);

		cc.reportEquality(f_x, g_z);

		assertTrue(cc.getEqualityStatus(f_x, g_z) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(f_z, g_x) == Equality.EQUAL);

		cc.reportEquality(x, y);

		assertTrue(cc.getEqualityStatus(x, g_z) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(y, f_y) == Equality.EQUAL);
	}


	@Test
	public void test3() {
		final CongruenceClosure<StringCCElement, String> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getFuncAppElement("f", x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getFuncAppElement("g", x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getFuncAppElement("f", y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getFuncAppElement("g", y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getFuncAppElement("f", z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getFuncAppElement("g", z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		cc.reportDisequality(f_x, f_y);
		assertTrue(cc.getEqualityStatus(f_x, f_y) == Equality.NOT_EQUAL);
		assertTrue(cc.getEqualityStatus(x, y) == Equality.NOT_EQUAL);

	}

	@Test
	public void test4() {
		final CongruenceClosure<StringCCElement, String> cc = new CongruenceClosure<>();

		final StringElementFactory factory = new StringElementFactory();

		final StringCCElement x = factory.getBaseElement("x");
		cc.getRepresentativeAndAddElementIfNeeded(x);
		final StringCCElement f_x = factory.getFuncAppElement("f", x);
		cc.getRepresentativeAndAddElementIfNeeded(f_x);
		final StringCCElement g_x = factory.getFuncAppElement("g", x);
		cc.getRepresentativeAndAddElementIfNeeded(g_x);

		final StringCCElement y = factory.getBaseElement("y");
		cc.getRepresentativeAndAddElementIfNeeded(y);
		final StringCCElement f_y = factory.getFuncAppElement("f", y);
		cc.getRepresentativeAndAddElementIfNeeded(f_y);
		final StringCCElement g_y = factory.getFuncAppElement("g", y);
		cc.getRepresentativeAndAddElementIfNeeded(g_y);

		final StringCCElement z = factory.getBaseElement("z");
		cc.getRepresentativeAndAddElementIfNeeded(z);
		final StringCCElement f_z = factory.getFuncAppElement("f", z);
		cc.getRepresentativeAndAddElementIfNeeded(f_z);
		final StringCCElement g_z = factory.getFuncAppElement("g", z);
		cc.getRepresentativeAndAddElementIfNeeded(g_z);

		cc.reportFunctionEquality("f", "g");
		assertTrue(cc.getEqualityStatus(f_x, g_x) == Equality.EQUAL);
		assertTrue(cc.getEqualityStatus(f_y, g_y) == Equality.EQUAL);

	}


}

abstract class AbstractCCElementFactory<
		ELEM extends ICongruenceClosureElement<ELEM, FUNCTION>,
//		FUNCTION extends ICongruenceClosureFunction,
		FUNCTION,
		CONTENT> {

	Map<CONTENT, ELEM> mContentToBaseElem = new HashMap<>();
	NestedMap2<FUNCTION, List<ELEM>, ELEM> mFunctionToArgsToFuncAppElem = new NestedMap2<>();

	protected abstract ELEM newBaseElement(CONTENT c);
	protected abstract ELEM newFuncAppElement(FUNCTION f, List<ELEM> args);

	ELEM getBaseElement(final CONTENT content) {
		ELEM be = mContentToBaseElem.get(content);
		if (be == null) {
			be = newBaseElement(content);
			mContentToBaseElem.put(content, be);
		}
		return be;
	}

	ELEM getFuncAppElement(final FUNCTION func,  final ELEM... arguments) {
		return getFuncAppElement(func, Arrays.asList(arguments));
	}

	ELEM getFuncAppElement(final FUNCTION func, final List<ELEM> arguments) {
		ELEM fae = mFunctionToArgsToFuncAppElem.get(func, arguments);
		if (fae == null) {
			fae = newFuncAppElement(func, arguments);
			mFunctionToArgsToFuncAppElem.put(func, arguments, fae);
		}
		for (final ELEM arg : arguments) {
			arg.addParent(fae);
		}
		return fae;
	}

}

class StringElementFactory extends AbstractCCElementFactory<StringCCElement, String, String> {

	@Override
	protected StringCCElement newBaseElement(final String c) {
		return new StringCCElement(c);
	}

	@Override
	protected StringCCElement newFuncAppElement(final String f, final List<StringCCElement> args) {
		return new StringCCElement(f, args);
	}

}

class StringCCElement implements ICongruenceClosureElement<StringCCElement, String>{

	private final boolean mIsFunctionApplication;
	private final String mName;
	private final String mAppliedFunction;
	private final List<StringCCElement> mArguments;

	private final Set<StringCCElement> mParents = new HashSet<>();

	public StringCCElement(final String name) {
		mIsFunctionApplication = false;
		mName = name;
		mAppliedFunction = null;
		mArguments = null;
	}

	public StringCCElement(final String appliedFunction, final List<StringCCElement> arguments) {
		mIsFunctionApplication = true;
		mName = null;
		mAppliedFunction = appliedFunction;
		mArguments = arguments;
	}


	@Override
	public Set<StringCCElement> getParents() {
		return mParents;
	}

	@Override
	public boolean isFunctionApplication() {
		return mIsFunctionApplication;
	}

	@Override
	public String getAppliedFunction() {
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
	public void addParent(final StringCCElement parent) {
		mParents.add(parent);
	}
}



//class StringCCFunction implements ICongruenceClosureFunction {
//
//	final String mName;
//
//	public StringCCFunction(final String name) {
//		mName = name;
//	}
//
//	@Override
//	public String toString() {
//		return mName;
//	}
//}