package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public abstract class AbstractCCElementFactory<ELEM extends ICongruenceClosureElement<ELEM>, CONTENT> {

	final Map<CONTENT, ELEM> mContentToBaseElem = new HashMap<>();
	final NestedMap2<ELEM, ELEM, ELEM> mFunctionToArgToFuncAppElem = new NestedMap2<>();

	protected abstract ELEM newBaseElement(CONTENT c);
	protected abstract ELEM newFuncAppElement(ELEM f, ELEM arg);

	public ELEM getBaseElement(final CONTENT content) {
		return getBaseElement(content, false);
	}

	public ELEM getBaseElement(final CONTENT content, final boolean forceExisting) {
		ELEM be = mContentToBaseElem.get(content);
		if (be == null) {
			if (forceExisting) {
				throw new IllegalStateException();
			}
			be = newBaseElement(content);
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
			func.addParent(fae);
			argument.addParent(fae);
			mFunctionToArgToFuncAppElem.put(func, argument, fae);
		}
		return fae;
	}
}