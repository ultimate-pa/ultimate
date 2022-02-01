package de.uni_freiburg.informatik.ultimate.lib.chc;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public abstract class HcVar implements IProgramVar {

	private final TermVariable mTermVariable;

	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;

	private final String mGloballyUniqueId;

	private final String mProcName;

	private final boolean mIsGlobal;

	private String mComment;


	HcVar(final String globallyUniqueId, final TermVariable termVariable, final ApplicationTerm defaultConstant,
			final ApplicationTerm primedConstant, final boolean isGlobal, final String procName) {
		mProcName = procName;
		mIsGlobal = isGlobal;
		mGloballyUniqueId = globallyUniqueId;
		mTermVariable = termVariable;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedConstant;
	}

	@Override
	public Term getTerm() {
		return mTermVariable;
	}

	@Override
	public boolean isGlobal() {
		return mIsGlobal;
	}

	@Override
	public String getGloballyUniqueId() {
		return mGloballyUniqueId;
	}

	@Override
	public String getProcedure() {
		return mProcName;
	}

	@Override
	public boolean isOldvar() {
		return false;
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
	public String toString() {
		return "HcVar:" + mGloballyUniqueId;
	}

	public void setComment(final String comment) {
		mComment = comment;
	}

	public String getComment() {
		return mComment;
	}

	public boolean hasComment() {
		return mComment != null;
	}
}
