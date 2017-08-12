package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public abstract class AbstractCCElementFactory<ELEM extends ICongruenceClosureElement<ELEM, FUNCTION>,
		FUNCTION, CONTENT> {

	final Map<CONTENT, ELEM> mContentToBaseElem = new HashMap<>();
	final NestedMap2<FUNCTION, List<ELEM>, ELEM> mFunctionToArgsToFuncAppElem = new NestedMap2<>();

	protected abstract ELEM newBaseElement(CONTENT c);
	protected abstract ELEM newFuncAppElement(FUNCTION f, List<ELEM> args);

	public ELEM getBaseElement(final CONTENT content) {
		ELEM be = mContentToBaseElem.get(content);
		if (be == null) {
			be = newBaseElement(content);
			mContentToBaseElem.put(content, be);
		}
		return be;
	}

	public ELEM getFuncAppElement(final FUNCTION func,  final ELEM... arguments) {
		return getFuncAppElement(func, Arrays.asList(arguments));
	}

	public ELEM getFuncAppElement(final FUNCTION func, final List<ELEM> arguments) {
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