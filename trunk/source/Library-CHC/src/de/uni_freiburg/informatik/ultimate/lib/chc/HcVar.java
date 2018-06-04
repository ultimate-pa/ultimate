package de.uni_freiburg.informatik.ultimate.lib.chc;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public abstract class HcVar implements IProgramVar {


	/**
	 *
	 */
	private static final long serialVersionUID = 5293174270985171626L;

	private final TermVariable mTermVariable;

	/**
	 * The sort of the TermVariable and constants
	 *  --> this is a field just because it is part of this HCOutVar's identity.
	 */
	private final Sort mSort;

	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;

	private final String mGloballyUniqueId;

	private final HcPredicateSymbol mPredSymbol;

	private final String mProcName;

	private final int mIndex;

	private final boolean mIsGlobal;


	HcVar(final boolean headNotBody, final HcPredicateSymbol predSym, final int index, final Sort sort,
			final ManagedScript mgdScript, final Object lockOwner) {
		mPredSymbol = predSym;
		mProcName = HornUtilConstants.sanitzePredName(predSym.getName());
		mIndex = index;
		mSort = sort;

		mIsGlobal = headNotBody;

		mGloballyUniqueId =
				HornUtilConstants.computeNameForHcVar(headNotBody ?
						HornUtilConstants.HEADVARPREFIX :
							HornUtilConstants.BODYVARPREFIX,
				predSym, index, sort.toString());
		mTermVariable = mgdScript.variable(mGloballyUniqueId, sort);
		mDefaultConstant = ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, mGloballyUniqueId);
		mPrimedConstant = ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, mGloballyUniqueId);
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

}
