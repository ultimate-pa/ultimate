package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;

public class CFunction extends CType {
	
	CType mResultType;

	CDeclaration[] mParamTypes;
	
	boolean mTakesVarArgs;

	public CFunction(CType resultType, CDeclaration[] paramTypes, boolean takesVarArgs) {
        super(false, false, false, false); //FIXME: integrate those flags
		mResultType = resultType;
		mParamTypes = paramTypes;
		mTakesVarArgs = takesVarArgs;
	}
	
	public CType getResultType() {
		return mResultType;
	}

	public CDeclaration[] getParameterTypes() {
		return mParamTypes;
	}
	
	public boolean takesVarArgs() {
		return mTakesVarArgs;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CFunction: ");
		String times = "";
		for (int i = 0; i < mParamTypes.length; i++) {
			sb.append(mParamTypes[i].toString());
			sb.append(times);
			times = " x ";
		}
		if (mTakesVarArgs)
			sb.append(" x ...");
		sb.append(" -> ");
		sb.append(mResultType.toString());
		return sb.toString();
//		return "CFunction:";
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof CFunction)) {
			return false;
		}
		CFunction other = (CFunction) o;
		if (this.mParamTypes.length != other.mParamTypes.length)
			return false;
		boolean result = true;
		result &= this.mResultType.equals(other.mResultType);
		for (int i = 0; i < mParamTypes.length; i++)
			result &= this.mParamTypes[i].getType().equals(other.mParamTypes[i].getType());
		result &= this.mTakesVarArgs == other.mTakesVarArgs;
		return result;
	}
}
