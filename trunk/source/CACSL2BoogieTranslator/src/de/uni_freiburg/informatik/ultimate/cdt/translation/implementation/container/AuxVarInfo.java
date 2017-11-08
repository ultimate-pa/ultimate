package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;

/**
 * We often need to deal with auxiliary variables during translation.
 * Several objects may be related to an auxvar: A declaration, a LeftHandSide, an Expression, ...
 * This class stores all of these of one auxvar.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class AuxVarInfo {

	private final VariableDeclaration mVarDec;
	private final VariableLHS mLhs;
	private final IdentifierExpression mExp;

	public AuxVarInfo(final VariableDeclaration varDec, final VariableLHS lhs, final IdentifierExpression exp) {
		mVarDec = varDec;
		mLhs = lhs;
		mExp = exp;
	}

	public VariableDeclaration getVarDec() {
		return mVarDec;
	}

	public VariableLHS getLhs() {
		return mLhs;
	}

	public IdentifierExpression getExp() {
		return mExp;
	}
}
