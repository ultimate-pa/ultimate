package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class HybridProgramVar implements IProgramVar {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 3326754135474906040L;
	private final TermVariable mTermVariable;
	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;
	private final String mId;
	private final String mProcedure;
	
	public HybridProgramVar(TermVariable termVariable, ApplicationTerm defaultConstant, ApplicationTerm primedConstant,
			String id, String procedure) {
		mTermVariable = termVariable;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedConstant;
		mId = id;
		mProcedure = procedure;
	}
	
	@Override
	public TermVariable getTermVariable() {
		return mTermVariable;
	}
	
	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}
	
	@Override
	public ApplicationTerm getPrimedConstant() {
		return mPrimedConstant;
	}
	
	@Override
	public Term getTerm() {
		return null;
	}
	
	@Override
	public boolean isGlobal() {
		// TODO Auto-generated method stub
		return false;
	}
	
	@Override
	public String getGloballyUniqueId() {
		// TODO Auto-generated method stub
		return mId;
	}
	
	@Override
	public String getProcedure() {
		// TODO Auto-generated method stub
		return mProcedure;
	}
	
	@Override
	public boolean isOldvar() {
		// TODO Auto-generated method stub
		return false;
	}
	
	@Override
	public String toString() {
		String str = "(ID: " + mId;
		// str += ", TV: " + mTermVariable;
		// str += ", Procedure: " + mProcedure;
		// str += ", PrimedConst: " + mPrimedConstant;
		// str += ", DefaultConst: " + mDefaultConstant;
		str += ")";
		return str;
	}
	
}
