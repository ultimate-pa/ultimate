package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

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
			sb.append(times);
			sb.append(mParamTypes[i].getType().toString());
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
	
	public String functionSignatureAsProcedureName() {
		StringBuilder sb = new StringBuilder();
		sb.append("##fun~");
		String times = "";
		for (int i = 0; i < mParamTypes.length; i++) {
			sb.append(times);
			sb.append(mParamTypes[i].getType().toString());
			times = "~X~";
		}
		if (mTakesVarArgs)
			sb.append("X~varArgs~");
		sb.append("~TO~");
		sb.append(mResultType.toString());
		return sb.toString();
	}

	@Override
	public boolean isCompatibleWith(CType o) {
		if (o instanceof CPrimitive &&
				((CPrimitive) o).getType() == PRIMITIVE.VOID)
			return true;	
		
		if (!(o instanceof CFunction)) {
			return false;
		}
		CFunction other = (CFunction) o;
		if (this.mParamTypes.length != other.mParamTypes.length)
			return false;
		boolean result = true;
		result &= this.mResultType.isCompatibleWith(other.mResultType);
		for (int i = 0; i < mParamTypes.length; i++)
			result &= this.mParamTypes[i].getType().isCompatibleWith(other.mParamTypes[i].getType());
		result &= this.mTakesVarArgs == other.mTakesVarArgs;
		return result;
	}
	
	@Override
	public int hashCode() {
		int result = HashUtils.hashJenkins(31, mResultType);
		CType[] pTypes = new CType[mParamTypes.length];
		for (int i = 0; i < pTypes.length; i++) 
			result = HashUtils.hashJenkins(result, mParamTypes[i].getType());
//			pTypes[i] = mParamTypes[i].getType();
		result = HashUtils.hashJenkins(result, mTakesVarArgs);
		return result;
//		return HashUtils.hashJenkins(31, mResultType, mTakesVarArgs, pTypes);
//		return 0;
	}
}
