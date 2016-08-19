package de.uni_freiburg.informatik.ultimate.lassoranker.mapelimination;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;

public interface ApplicationTermTemplate {
	public Term getTerm(final ArrayIndex arguments);

	public Object getIdentifier();
}

class SelectTemplate implements ApplicationTermTemplate {
	private final Term mArray;
	private final Script mScript;

	public SelectTemplate(final Term array, final Script script) {
		mArray = array;
		mScript = script;
	}

	@Override
	public Object getIdentifier() {
		return mArray;
	}

	@Override
	public Term getTerm(final ArrayIndex arguments) {
		return SmtUtils.multiDimensionalSelect(mScript, mArray, arguments);
	}

	@Override
	public boolean equals(final Object other) {
		if (other instanceof SelectTemplate) {
			final SelectTemplate template = (SelectTemplate) other;
			return mArray.equals(template.mArray);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mArray.hashCode();
	}

	@Override
	public String toString() {
		return "(select " + mArray.toString() + " ...)";
	}
}

class FunctionTemplate implements ApplicationTermTemplate {
	private final String mFunctionName;
	private final Script mScript;

	public FunctionTemplate(final String functionName, final Script script) {
		mFunctionName = functionName;
		mScript = script;
	}

	@Override
	public Term getTerm(final ArrayIndex arguments) {
		final Term[] params = arguments.toArray(new Term[arguments.size()]);
		return mScript.term(mFunctionName, params);
	}

	@Override
	public boolean equals(final Object other) {
		if (other instanceof FunctionTemplate) {
			final FunctionTemplate template = (FunctionTemplate) other;
			return mFunctionName.equals(template.mFunctionName);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mFunctionName.hashCode();
	}

	@Override
	public String toString() {
		return "(" + mFunctionName + " ...)";
	}

	@Override
	public Object getIdentifier() {
		return mFunctionName;
	}
}
