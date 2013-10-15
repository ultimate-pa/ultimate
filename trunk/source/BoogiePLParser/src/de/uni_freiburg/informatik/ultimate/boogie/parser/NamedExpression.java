package de.uni_freiburg.informatik.ultimate.boogie.parser;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

/**
 * Temporary class to represent a pair of a named and an expression. This
 * is used temporarily for StructConstructor expressions.
 * 
 * @author Jochen Hoenicke
 */
public class NamedExpression {
	String mName;
	Expression mExpr;
	
	public NamedExpression(String name, Expression expr) {
		mName = name;
		mExpr = expr;
	}

	public String getName() {
		return mName;
	}

	public Expression getExpression() {
		return mExpr;
	}
}
