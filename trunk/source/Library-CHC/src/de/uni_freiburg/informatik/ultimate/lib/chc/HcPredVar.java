package de.uni_freiburg.informatik.ultimate.lib.chc;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public abstract class HcPredVar extends HcVar {


	/**
	 * The sort of the TermVariable and constants
	 *  --> this is a field just because it is part of this HCOutVar's identity.
	 */
	private final Sort mSort;

	private final HcPredicateSymbol mPredSymbol;

	private final int mIndex;

	/**
	 *
	 * @param globallyUniqueId
	 * @param headNotBody TODO this determines isGlobal -- why???
	 * @param predSym
	 * @param index
	 * @param sort
	 * @param mgdScript
	 * @param lockOwner
	 */
	HcPredVar(final String globallyUniqueId, final boolean headNotBody, final HcPredicateSymbol predSym, final int index, final Sort sort,
			final ManagedScript mgdScript, final Object lockOwner) {
		super(globallyUniqueId,
				mgdScript.variable(globallyUniqueId, sort),
				ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, globallyUniqueId),
				ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, globallyUniqueId),
				headNotBody,
				HornUtilConstants.sanitzePredName(predSym.getName())
				);

		mPredSymbol = predSym;
//		mProcName = HornUtilConstants.sanitzePredName(predSym.getName());
		mIndex = index;
		mSort = sort;

//		mIsGlobal = headNotBody;

//		mGloballyUniqueId = globallyUniqueId;
//				HornUtilConstants.computeNameForHcVar(headNotBody ?
//						HornUtilConstants.HEADVARPREFIX :
//							HornUtilConstants.BODYVARPREFIX,
//				predSym, index, sort.toString());
//		mTermVariable = mgdScript.variable(mGloballyUniqueId, sort);
//		mDefaultConstant = ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, mGloballyUniqueId);
//		mPrimedConstant = ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, mGloballyUniqueId);
	}

	public int getIndex() {
		return mIndex;
	}

}
