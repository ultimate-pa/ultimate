package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class MemoryModelDeclarationInfo {
	private final MemoryModelDeclarations mMmd;
	private final BoogieType mBoogieType;

	public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		mMmd = mmd;
		mBoogieType = null;
	}

	public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd, final BoogieType boogieType) {
		mMmd = mmd;
		mBoogieType = boogieType;
	}

	IdentifierExpression constructIdentifierExpression(final ILocation loc) {
		return ExpressionFactory.constructIdentifierExpression(loc, mBoogieType, mMmd.getName(),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	VariableLHS constructVariableLHS(final ILocation loc) {
		return ExpressionFactory.constructVariableLHS(loc, mBoogieType, mMmd.getName(),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	BoogieType getBoogieType() {
		if (mBoogieType == null) {
			throw new IllegalStateException();
		}
		return mBoogieType;
	}
}
