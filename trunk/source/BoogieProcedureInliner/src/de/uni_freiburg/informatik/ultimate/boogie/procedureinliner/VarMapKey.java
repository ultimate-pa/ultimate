package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;

/**
 * Key for the map from old to new variable identifiers, used while creating an inline version of a Boogie procedure.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarMapKey {
	
	private String mVarId;
	private DeclarationInformation mDeclInfo;
	private String mInOldExprOfProc;

	/**
	 * Convenience constructor for variables, which didn't appear in (inlined) old() expressions.
	 * @param varId Original identifier of the variable.
	 * @param declInfo Original DeclarationInformation of the variable.
	 */
	public VarMapKey(String varId, DeclarationInformation declInfo) {
		this(varId, declInfo, null);
	}
	
	/**
	 * Creates a new key.
	 * @param varId Original identifier of the variable.
	 * @param declInfo Original DeclarationInformation of the variable.
	 * @param inOldExprOfProc The variable appeared inside an (inlined) old() expression,
	 *                        inside the Procedure with the given identifier.
	 *                        {@code null}, iff the variable wasn't inside an old() expression.
	 */
	public VarMapKey(String varId, DeclarationInformation declInfo, String inOldExprOfProc) {
		mVarId = varId;
		mDeclInfo = declInfo;
		mInOldExprOfProc = inOldExprOfProc;
	}

	/** @return Original identifier of the variable. */
	public String getVarId() {
		return mVarId;
	}

	/** @return Original DeclarationInformation of the variable. */
	public DeclarationInformation getDeclInfo() {
		return mDeclInfo;
	}
	
	/**
	 * @return Identifier of the procedure, in which the variable appeared inside an (inlined) old() expression.
	 *         {@code null}, iff the variable didn't appear in an (inlined) old() expression.
	 */
	public String getInOldExprOfProc() {
		return mInOldExprOfProc;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDeclInfo == null) ? 0 : mDeclInfo.hashCode());
		result = prime * result + ((mInOldExprOfProc == null) ? 0 : mInOldExprOfProc.hashCode());
		result = prime * result + ((mVarId == null) ? 0 : mVarId.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		VarMapKey other = (VarMapKey) obj;
		if (mDeclInfo == null) {
			if (other.mDeclInfo != null)
				return false;
		} else if (!mDeclInfo.equals(other.mDeclInfo))
			return false;
		if (mInOldExprOfProc == null) {
			if (other.mInOldExprOfProc != null)
				return false;
		} else if (!mInOldExprOfProc.equals(other.mInOldExprOfProc))
			return false;
		if (mVarId == null) {
			if (other.mVarId != null)
				return false;
		} else if (!mVarId.equals(other.mVarId))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "VarMapKey[" + mVarId + " " + mDeclInfo + " " + mInOldExprOfProc + "]";
	}

}
