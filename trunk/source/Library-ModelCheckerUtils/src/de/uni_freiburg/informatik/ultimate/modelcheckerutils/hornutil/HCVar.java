package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class HCVar implements IProgramVar {
	private final HornClausePredicateSymbol predicate;
	private final TermVariable termVariable;
	private final int idx;
	
	public HCVar(HornClausePredicateSymbol pr, int pos, TermVariable v) {
		predicate = pr;
		idx = pos;
		termVariable = v;
	}
	
	@Override
	public TermVariable getTermVariable() {
		return termVariable;
	}
	
	@Override
	public String toString() {
		return predicate.getName() + "{" + idx + "}" + ":" + termVariable.toString();
	}
	
	@Override
	public String getGloballyUniqueId() {
		return String.format("%s_%d", predicate.getName(), idx);
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
		return getGloballyUniqueId().hashCode();
	}
}
