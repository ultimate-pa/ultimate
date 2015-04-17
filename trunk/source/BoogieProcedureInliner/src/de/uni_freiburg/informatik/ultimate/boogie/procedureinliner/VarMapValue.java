package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;

/**
 * Value for the map from old to new variable identifiers, used while creating an inline version of a Boogie procedure.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarMapValue {

	private String mVarId;
	private DeclarationInformation mDeclInfo;
	
	/**
	 * Creates a new VarMapValue, containing the new identifier and DeclarationInformation of a variable.
	 * @param varId New identifier of the variable.
	 * @param declInfo New DeclarationInformation of the variable.
	 */
	public VarMapValue(String varId, DeclarationInformation declInfo) {
		super();
		mVarId = varId;
		mDeclInfo = declInfo;
	}

	public String getVarId() {
		return mVarId;
	}

	public DeclarationInformation getDeclInfo() {
		return mDeclInfo;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDeclInfo == null) ? 0 : mDeclInfo.hashCode());
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
		VarMapValue other = (VarMapValue) obj;
		if (mDeclInfo == null) {
			if (other.mDeclInfo != null)
				return false;
		} else if (!mDeclInfo.equals(other.mDeclInfo))
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
		return "VarMapValue [mVarId=" + mVarId + ", mDeclInfo=" + mDeclInfo + "]";
	}
}
