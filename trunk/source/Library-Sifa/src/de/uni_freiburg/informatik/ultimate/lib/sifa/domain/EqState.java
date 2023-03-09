package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqState implements IAbstractState<EqState> {
	private final EqConstraint<EqNode> mConstraint;

	public EqState(final EqConstraint<EqNode> constraint) {
		mConstraint = constraint;
	}

	@Override
	public Term toTerm(final Script script) {
		return mConstraint.getTerm(script);
	}

	@Override
	public EqState join(final EqState other) {
		return new EqState(mConstraint.join(other.mConstraint));
	}

	@Override
	public EqState widen(final EqState other) {
		return join(other);
	}

	@Override
	public boolean isBottom() {
		return mConstraint.isBottom();
	}

}
