package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingIntermediateState;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqIntermediateState implements IEqualityProvidingIntermediateState {

	private final EqDisjunctiveConstraint<EqNode> mConstraint;

	public EqIntermediateState(final EqDisjunctiveConstraint<EqNode> constraint) {
		mConstraint = constraint;
	}

	@Override
	public boolean areEqual(final Term t1, final Term t2) {
		return mConstraint.areEqual(t1, t2);
	}

	@Override
	public boolean areUnequal(final Term t1, final Term t2) {
		return mConstraint.areUnequal(t1, t2);
	}

//	@Override
//	public IEqualityProvidingIntermediateState join(final IEqualityProvidingIntermediateState other) {
//		// TODO Auto-generated method stub
//		return null;
//	}

	@Override
	public boolean isBottom() {
		return mConstraint.isBottom();
	}

	@Override
	public Set<Term> getSetConstraintForExpression(final Term locArraySelect) {
		final Set<Term> result = mConstraint.getSetConstraintForExpression(locArraySelect);
		return result;
	}

}
