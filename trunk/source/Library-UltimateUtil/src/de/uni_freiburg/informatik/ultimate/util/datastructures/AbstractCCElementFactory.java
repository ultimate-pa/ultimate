package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public abstract class AbstractCCElementFactory<ELEM extends ICongruenceClosureElement<ELEM>, CONTENT> {

	final Map<CONTENT, ELEM> mContentToBaseElem = new HashMap<>();
//	final NestedMap2<ELEM, List<ELEM>, ELEM> mFunctionToArgsToFuncAppElem = new NestedMap2<>();
	final NestedMap2<ELEM, ELEM, ELEM> mFunctionToArgToFuncAppElem = new NestedMap2<>();

//	protected abstract ELEM newBaseElement(CONTENT c, boolean isFunction);
//	protected abstract ELEM newFuncAppElement(ELEM f, List<ELEM> args, boolean isFunction);
	protected abstract ELEM newBaseElement(CONTENT c);
//	protected abstract ELEM newFuncAppElement(ELEM f, List<ELEM> args);
	protected abstract ELEM newFuncAppElement(ELEM f, ELEM arg);

//	public ELEM getFunctionBaseElement(final CONTENT content) {
//		return getBaseElement(content, true, false);
//	}
//
//	public ELEM getFunctionBaseElement(final CONTENT content, final boolean forceExisting) {
//		return getBaseElement(content, true, forceExisting);
//	}
//
//	public ELEM getNonFunctionBaseElement(final CONTENT content) {
//		return getBaseElement(content, false, false);
//	}
//
//	public ELEM getNonFunctionBaseElement(final CONTENT content, final boolean forceExisting) {
//		return getBaseElement(content, false, forceExisting);
//	}

	public ELEM getBaseElement(final CONTENT content) {
		return getBaseElement(content, false);
	}

//	private ELEM getBaseElement(final CONTENT content, final boolean isFunction, final boolean forceExisting) {
	public ELEM getBaseElement(final CONTENT content, final boolean forceExisting) {
		ELEM be = mContentToBaseElem.get(content);
		if (be == null) {
			if (forceExisting) {
				throw new IllegalStateException();
			}
//			be = newBaseElement(content, isFunction);
			be = newBaseElement(content);
			mContentToBaseElem.put(content, be);
		}
//		if (be.isFunction() != isFunction) {
//			throw new AssertionError("did we attempt to build the same element twice, once with isFunction true, and"
//					+ " once with false??");
//		}
		return be;
	}

//	public ELEM getFunctionFuncAppElement(final ELEM func,  final ELEM... arguments) {
//		return getFuncAppElement(func, Arrays.asList(arguments), true, false);
//	}
//
//	public ELEM getFunctionFuncAppElement(final ELEM func, final List<ELEM> arguments) {
//		return getFuncAppElement(func, arguments, true, false);
//	}
//
//	public ELEM getNonFunctionFuncAppElement(final ELEM func,  final ELEM... arguments) {
//		return getFuncAppElement(func, Arrays.asList(arguments), false, false);
//	}
//
//	public ELEM getNonFunctionFuncAppElement(final ELEM func, final List<ELEM> arguments) {
//		return getFuncAppElement(func, arguments, false, false);
//	}


//	public abstract ELEM getFuncAppElementDetermineIsFunctionYourself(final ELEM func,
//			final List<ELEM> arguments);


//	public ELEM getFuncAppElement(final ELEM func,  final ELEM... arguments) {
//		return getFuncAppElement(func, Arrays.asList(arguments), false);
//	}
//
	public ELEM getOrConstructFuncAppElement(final ELEM func, final ELEM argument) {
		return getFuncAppElement(func, argument, false);
	}

//	public ELEM getFuncAppElement(final ELEM func, final List<ELEM> arguments,
	public ELEM getFuncAppElement(final ELEM func, final ELEM argument,
			final boolean forceExisting) {
		ELEM fae = mFunctionToArgToFuncAppElem.get(func, argument);
		if (fae == null) {
			if (forceExisting) {
				throw new IllegalStateException();
			}
//			fae = newFuncAppElement(func, arguments, isFunction);
//			fae = newFuncAppElement(func, arguments);
			fae = newFuncAppElement(func, argument);
			func.addParent(fae);
			argument.addParent(fae);
			mFunctionToArgToFuncAppElem.put(func, argument, fae);
		}
//		if (fae.isFunction() != isFunction) {
//			throw new AssertionError("did we attempt to build the same element twice, once with isFunction true, and"
//					+ " once with false??");
//		}
		return fae;
	}

//	private ELEM buildFuncAppNodeElement(final ELEM appliedFunction,
//			final List<ELEM> arguments) {//, final boolean isFunction) {
//
//		ELEM result = appliedFunction;
//
//		for (final ELEM arg : arguments) {
////			result = getOrConstructNode(buildSelectTerm(result, arg));
//			//			result = new EqFunctionApplicationNode(result, arg, buildSelectTerm(result, arg), this);
//			result = newFuncAppElement(result, arg);
//		}
//
//		return result;
//	}

//	public boolean hasBaseElement(final CONTENT cont) {
//		return mContentToBaseElem.get(cont) != null;
//	}
//
//	public boolean hasFuncAppElement(final ELEM func, final List<ELEM> elems) {
//		return mFunctionToArgsToFuncAppElem.get(func, elems) != null;
//	}

}