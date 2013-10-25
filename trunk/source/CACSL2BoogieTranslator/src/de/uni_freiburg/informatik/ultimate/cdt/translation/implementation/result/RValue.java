package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

public class RValue extends LRValue {

	Expression value;
	
	/**
	 * The Value in a ResultExpression that may only be used on the 
	 * right-hand side of an assignment, i.e. its corresponding
	 * memory cell may only be read.
	 * @param value
	 */
	public RValue(Expression value, CType cType) {
		this.value = value;
		this.cType = cType;
	}

	public Expression getValue() {
		return this.value;
	}
}
