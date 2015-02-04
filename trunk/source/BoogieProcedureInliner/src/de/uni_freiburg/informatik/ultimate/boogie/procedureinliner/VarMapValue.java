package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * Value for the map from old to new variable identifiers, used while creating an inline version of a Boogie procedure.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarMapValue {

	private String mVarId;
	private IType mType;
	
	/**
	 * Creates a new VarMapValue, containing the new identifier and type of a variable.
	 * @param varId New identifier of the variable.
	 * @param type New type of the variable.
	 */
	public VarMapValue(String varId, IType type) {
		super();
		mVarId = varId;
		mType = type;
	}

	public String getmVarId() {
		return mVarId;
	}

	public IType getmType() {
		return mType;
	}

	@Override
	public String toString() {
		return "VarMapValue [mVarId=" + mVarId + ", mType=" + mType + "]";
	}

}
