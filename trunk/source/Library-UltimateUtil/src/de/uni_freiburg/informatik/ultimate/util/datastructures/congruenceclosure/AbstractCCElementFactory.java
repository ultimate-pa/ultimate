package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public abstract class AbstractCCElementFactory<ELEM extends ICongruenceClosureElement<ELEM>, CONTENT> {

	final Map<CONTENT, ELEM> mContentToBaseElem = new HashMap<>();
	final NestedMap2<ELEM, ELEM, ELEM> mFunctionToArgToFuncAppElem = new NestedMap2<>();

	protected abstract ELEM newBaseElement(CONTENT c, boolean isLiteral);
	protected abstract ELEM newFuncAppElement(ELEM f, ELEM arg);

	public ELEM getBaseElement(final CONTENT content) {
		return getBaseElement(content, false);
	}

	public ELEM getBaseElement(final CONTENT content, final boolean isLiteral) {
		ELEM be = mContentToBaseElem.get(content);
		if (be == null) {
			be = newBaseElement(content, isLiteral);
			mContentToBaseElem.put(content, be);
		}
		return be;
	}

	public ELEM getOrConstructFuncAppElement(final ELEM func, final ELEM argument) {
		return getFuncAppElement(func, argument, false);
	}

	public ELEM getFuncAppElement(final ELEM func, final ELEM argument,
			final boolean forceExisting) {
		ELEM fae = mFunctionToArgToFuncAppElem.get(func, argument);
		if (fae == null) {
			if (forceExisting) {
				throw new IllegalStateException();
			}
			fae = newFuncAppElement(func, argument);
			mFunctionToArgToFuncAppElem.put(func, argument, fae);
		}
		return fae;
	}
}