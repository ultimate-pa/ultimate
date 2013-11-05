package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;

public class CFunction extends CType {

	public CFunction(IASTDeclSpecifier cDeclSpec) {
		super(cDeclSpec);
	}

	@Override
	public String toString() {
		return "CFunction";
	}

}
