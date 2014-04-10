package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

public class RValue extends LRValue {

	public Expression value;
	
	/**
	 * The Value in a ResultExpression that may only be used on the 
	 * right-hand side of an assignment, i.e. its corresponding
	 * memory cell may only be read.
	 * @param value
	 */
	public RValue(Expression value, CType cType) {
		this(value, cType, false);
//		this(value, cType, false, false, false);
	}
	
	/**
	 * The Value in a ResultExpression that may only be used on the 
	 * right-hand side of an assignment, i.e. its corresponding
	 * memory cell may only be read.
	 * @param value
	 */
	public RValue(Expression value, CType cType, boolean boogieBool) {
//	public RValue(Expression value, CType cType, boolean wrappedBool, boolean isPointer, boolean isOnHeap) {
		this.value = value;
		this.cType = cType;
		this.isBoogieBool = boogieBool;
		//this.isPointer = isPointer;
	}
	
	public RValue(RValue rval) {
		this(rval.value, rval.cType, rval.isBoogieBool);
//		this(rval.value, rval.cType, rval.isWrappedBool, rval.isPointer, rval.isOnHeap);
	}

	public Expression getValue() {
		return this.value;
	}
}
