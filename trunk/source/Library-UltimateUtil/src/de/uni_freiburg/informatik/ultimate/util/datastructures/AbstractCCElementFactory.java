package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public abstract class AbstractCCElementFactory<ELEM extends ICongruenceClosureElement<ELEM>, CONTENT> {

	final Map<CONTENT, ELEM> mContentToBaseElem = new HashMap<>();
	final NestedMap2<ELEM, List<ELEM>, ELEM> mFunctionToArgsToFuncAppElem = new NestedMap2<>();

	protected abstract ELEM newBaseElement(CONTENT c, boolean isFunction);
	protected abstract ELEM newFuncAppElement(ELEM f, List<ELEM> args, boolean isFunction);

	public ELEM getFunctionBaseElement(final CONTENT content) {
		return getBaseElement(content, true, false);
	}

	public ELEM getFunctionBaseElement(final CONTENT content, final boolean forceExisting) {
		return getBaseElement(content, true, forceExisting);
	}

	public ELEM getNonFunctionBaseElement(final CONTENT content) {
		return getBaseElement(content, false, false);
	}

	public ELEM getNonFunctionBaseElement(final CONTENT content, final boolean forceExisting) {
		return getBaseElement(content, false, forceExisting);
	}

	private ELEM getBaseElement(final CONTENT content, final boolean isFunction, final boolean forceExisting) {
		ELEM be = mContentToBaseElem.get(content);
		if (be == null) {
			if (forceExisting) {
				throw new IllegalStateException();
			}
			be = newBaseElement(content, isFunction);
			mContentToBaseElem.put(content, be);
		}
		if (be.isFunction() != isFunction) {
			throw new AssertionError("did we attempt to build the same element twice, once with isFunction true, and"
					+ " once with false??");
		}
		return be;
	}

	public ELEM getFunctionFuncAppElement(final ELEM func,  final ELEM... arguments) {
		return getFuncAppElement(func, Arrays.asList(arguments), true, false);
	}

	public ELEM getFunctionFuncAppElement(final ELEM func, final List<ELEM> arguments) {
		return getFuncAppElement(func, arguments, true, false);
	}

	public ELEM getNonFunctionFuncAppElement(final ELEM func,  final ELEM... arguments) {
		return getFuncAppElement(func, Arrays.asList(arguments), false, false);
	}

	public ELEM getNonFunctionFuncAppElement(final ELEM func, final List<ELEM> arguments) {
		return getFuncAppElement(func, arguments, false, false);
	}


	public abstract ELEM getFuncAppElementDetermineIsFunctionYourself(final ELEM func,
			final List<ELEM> arguments);

	private ELEM getFuncAppElement(final ELEM func, final List<ELEM> arguments, final boolean isFunction,
			final boolean forceExisting) {
		ELEM fae = mFunctionToArgsToFuncAppElem.get(func, arguments);
		if (fae == null) {
			if (forceExisting) {
				throw new IllegalStateException();
			}
			fae = newFuncAppElement(func, arguments, isFunction);
			mFunctionToArgsToFuncAppElem.put(func, arguments, fae);
		}
		if (fae.isFunction() != isFunction) {
			throw new AssertionError("did we attempt to build the same element twice, once with isFunction true, and"
					+ " once with false??");
		}
		return fae;
	}

	public boolean hasBaseElement(final CONTENT cont) {
		return mContentToBaseElem.get(cont) != null;
	}

	public boolean hasFuncAppElement(final ELEM func, final List<ELEM> elems) {
		return mFunctionToArgsToFuncAppElem.get(func, elems) != null;
	}

}