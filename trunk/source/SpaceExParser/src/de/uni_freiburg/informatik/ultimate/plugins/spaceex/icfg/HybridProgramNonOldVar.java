package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;

public class HybridProgramNonOldVar implements IProgramNonOldVar {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -5641559333840517863L;
	private final TermVariable mTermVariable;
	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;
	private final String mId;
	
	public HybridProgramNonOldVar(TermVariable termVariable, ApplicationTerm defaultConstant,
			ApplicationTerm primedConstant, String id) {
		mTermVariable = termVariable;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedConstant;
		mId = id;
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
	public String getIdentifier() {
		return mId;
	}
	
	@Override
	public IProgramOldVar getOldVar() {
		return null;
	}
	
}
