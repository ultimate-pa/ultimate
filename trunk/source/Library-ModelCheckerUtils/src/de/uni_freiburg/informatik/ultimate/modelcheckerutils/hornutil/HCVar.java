package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class HCVar implements IProgramVar {
	private static final long serialVersionUID = 1L;

	private final HornClausePredicateSymbol mPredicate;
	private final TermVariable mTermVariable;
	private final int mIdx;

	public HCVar(final HornClausePredicateSymbol pr, final int pos, final TermVariable v) {
		mPredicate = pr;
		mIdx = pos;
		mTermVariable = v;
	}

	@Override
	public TermVariable getTermVariable() {
		return mTermVariable;
	}

	@Override
	public String toString() {
		return mPredicate.getName() + "{" + mIdx + "}" + ":" + mTermVariable.toString();
	}

	@Override
	public String getGloballyUniqueId() {
		return String.format("%s_%d", mPredicate.getName(), mIdx);
	}

	@Override
	public String getProcedure() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isGlobal() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isOldvar() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term getTerm() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int hashCode() {
		// TODO: Sooooo expensive!! String is always recomputed. Also, override equals!!!
		return getGloballyUniqueId().hashCode();
	}
}
