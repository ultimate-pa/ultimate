package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

public class LocalLValue extends LRValue {

	LeftHandSide lhs;

	/**
	 * A Value inside a ResultExpression that is not stored on the heap, but as
	 * a normal Boogie Variable. It may be written (call getLHS()) or read (by
	 * making it to an RValue first).
	 * 
	 * @param expr
	 */
	public LocalLValue(LeftHandSide lhs) {
		this.lhs = lhs;
	}

	public LeftHandSide getLHS() {
		return lhs;
	}

	private Expression convertToExpression(LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return new IdentifierExpression(lhs.getLocation(), lhs.getType(),
					((VariableLHS) lhs).getIdentifier());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			Expression array = convertToExpression(alhs.getArray());
			return new ArrayAccessExpression(alhs.getLocation(), alhs.getType(), array,
					alhs.getIndices());
		} else if (lhs instanceof StructLHS) {
			StructLHS slhs = (StructLHS) lhs;
			Expression struct = convertToExpression(slhs.getStruct());
			return new StructAccessExpression(slhs.getLocation(), slhs.getType(), struct,
					slhs.getField());
		} else {
			throw new AssertionError("Strange LeftHandSide " + lhs);
		}
	}

	public Expression getValue() {
		return convertToExpression(lhs);
	}
}
