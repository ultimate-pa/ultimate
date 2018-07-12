package de.uni_freiburg.informatik.ultimate.pea2boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;

public interface IReqSymbolExpressionTable {
	
	public IdentifierExpression getIdentifierExpression(final String name);
}
