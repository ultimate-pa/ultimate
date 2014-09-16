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
		return "CFunction";
	}

}
