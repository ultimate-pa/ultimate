package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;

/**
 * Key for the map from old to new variable identifiers, used while creating an inline version of a Boogie procedure.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarMapKey {
	
	private String mVarId;
	private DeclarationInformation mDeclInfo;
	private IType mType;
	
	/**
	 * Creates a new key.
	 * @param varId Original identifier of the variable.
	 * @param declInfo Original DeclarationInformation of the variable.
	 * @param type Type of the variable.
	 */
	public VarMapKey(String varId, DeclarationInformation declInfo, IType type) {
		mVarId = varId;
		mDeclInfo = declInfo;
		mType = type;
	}

	/** @return Original identifier of the variable. */
	public String getVarId() {
		return mVarId;
	}

	/** @return Original DeclarationInformation of the variable. */
	public DeclarationInformation getDeclInfo() {
		return mDeclInfo;
	}

	/** @return Type of the variable. */
	public IType getType() {
		return mType;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDeclInfo == null) ? 0 : mDeclInfo.hashCode());
		result = prime * result + ((mType == null) ? 0 : mType.hashCode());
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
		if (mType == null) {
			if (other.mType != null)
				return false;
		} else if (!mType.equals(other.mType))
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
		return "VarMapKey [mVarId=" + mVarId + ", mDeclInfo=" + mDeclInfo + ", mType=" + mType + "]";
	}

}
