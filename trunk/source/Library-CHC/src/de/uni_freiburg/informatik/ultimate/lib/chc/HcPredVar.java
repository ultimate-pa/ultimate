package de.uni_freiburg.informatik.ultimate.lib.chc;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public abstract class HcPredVar extends HcVar {

	private final int mIndex;

	/**
	 *
	 * @param globallyUniqueId
	 * @param headNotBody
	 *            TODO this determines isGlobal -- why???
	 * @param predSym
	 * @param index
	 * @param sort
	 * @param mgdScript
	 * @param lockOwner
	 */
	HcPredVar(final String globallyUniqueId, final boolean headNotBody, final String procName, final int index,
			final Sort sort, final ManagedScript mgdScript, final Object lockOwner) {
		super(globallyUniqueId, mgdScript.variable(globallyUniqueId, sort),
				ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, globallyUniqueId),
				ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, globallyUniqueId), headNotBody,
				HornUtilConstants.sanitizePredName(procName));
		mIndex = index;
	}

	public int getIndex() {
		return mIndex;
	}

}
