/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;

/**
 * @author Thomas Lang
 *
 */
public class DefaultOperationTranslator implements IOperationTranslator {
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IOperationTranslator#opTranslation(de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public String opTranslation(BinaryExpression.Operator op, IType type1, IType type2) {
			if (op == BinaryExpression.Operator.COMPEQ) {
				// if
				// (binexp.getLeft().getType().equals(PrimitiveType.boolType))
				return "=";
				// else
				// return script.equals(translateTerm(binexp.getLeft()),
				// translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPGEQ) {
				return ">=";
			} else if (op == BinaryExpression.Operator.COMPGT) {
				return ">";
			} else if (op == BinaryExpression.Operator.COMPLEQ) {
				return "<=";
			} else if (op == BinaryExpression.Operator.COMPLT) {
				return "<";
			} else if (op == BinaryExpression.Operator.COMPNEQ) {
			    throw new UnsupportedOperationException();
				// } else if (op == BinaryExpression.Operator.COMPPO ){
				// return script.atom(partOrder,
				// translateTerm(binexp.getLeft()),
				// translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICAND) {
				return "and";
			} else if (op == BinaryExpression.Operator.LOGICOR) {
				return "or";
			} else if (op == BinaryExpression.Operator.LOGICIMPLIES) {
				return "=>";
			} else if (op == BinaryExpression.Operator.LOGICIFF) {
				return "=";
			} else if (op == BinaryExpression.Operator.ARITHDIV) {
				if (type1 instanceof PrimitiveType) {
					PrimitiveType primType = (PrimitiveType) type1;
					if (primType.getTypeCode() == PrimitiveType.INT) {
						return "div";
					} else if (primType.getTypeCode() == PrimitiveType.REAL) {
						return "/";
					} else {
						throw new AssertionError("ARITHDIV of this type not allowed");
					}
				} else {
					throw new AssertionError("ARITHDIV of this type not allowed");
				}
			} else if (op == BinaryExpression.Operator.ARITHMINUS) {
				return "-";
			} else if (op == BinaryExpression.Operator.ARITHMOD) {
				return "mod";
			} else if (op == BinaryExpression.Operator.ARITHMUL) {
			    return "*";
			} else if (op == BinaryExpression.Operator.ARITHPLUS) {
				return "+";
			} else if (op == BinaryExpression.Operator.BITVECCONCAT) {
				return "concat";
			} else {
				throw new AssertionError("Unsupported binary expression " + op);
			}
	}

	@Override
	public String opTranslation(Operator op, IType type) {
		if (op == UnaryExpression.Operator.LOGICNEG) {
			return "not";
		} else if (op == UnaryExpression.Operator.ARITHNEGATIVE) {
			// FunctionSymbol fun_symb = script.getFunction("-", intSort);
			return "-";
		} else
			throw new AssertionError("Unsupported unary expression " + op);
	}
}
