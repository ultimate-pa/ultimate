package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqAtomicConstantArrayNode extends EqAtomicBaseNode {

	private final EqNode mValue;

	public EqAtomicConstantArrayNode(final Term term, final boolean isLiteral,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final EqNode value) {
		super(term, isLiteral, eqNodeAndFunctionFactory, false);
		mValue = value;
	}

	@Override
	public boolean isConstantFunction() {
		return true;
	}

	/**
	 *
	 * @return the value that this constant array has at every index
	 */
	@Override
	public EqNode getConstantFunctionValue() {
		return mValue;
	}
}
