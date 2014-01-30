package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;

public class CFunction extends CType {
	
	CType mResultType;
	CDeclaration[] mParamTypes;

	public CFunction(CType resultType, CDeclaration[] paramTypes) {
        super(false, false, false, false); //FIXME: integrate those flags
		mResultType = resultType;
		mParamTypes = paramTypes;
	}
	
	public CDeclaration[] getParameterTypes() {
		return mParamTypes;
	}

	@Override
	public String toString() {
		return "CFunction";
	}

}
