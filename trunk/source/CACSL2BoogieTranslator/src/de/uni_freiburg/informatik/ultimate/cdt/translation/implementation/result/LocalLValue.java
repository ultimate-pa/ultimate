package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

public class LocalLValue extends LRValue {

	public LeftHandSide lhs;

	/**
	 * A Value inside a ResultExpression that is not stored on the heap, but as
	 * a normal Boogie Variable. It may be written (call getLHS()) or read (by
	 * making it to an RValue first).
	 * 
	 * @param expr
	 */
	public LocalLValue(LeftHandSide lhs, CType cType) {
		this(lhs, cType, false, false);
	}
	
	
	public LocalLValue(LeftHandSide lhs, CType cType, boolean wrappedBool, boolean isPtr) {
		this.lhs = lhs;
		this.cType = cType;
		this.isBoogieBool = wrappedBool;
		this.isPointer = isPtr;
	}

	public LocalLValue(LocalLValue llVal) {
		this(llVal.lhs, llVal.cType, llVal.isBoogieBool, llVal.isPointer);
	}
	
	public LeftHandSide getLHS() {
		return lhs;
	}

	public Expression getValue() {
		return CHandler.convertLHSToExpression(lhs);
	}
}
