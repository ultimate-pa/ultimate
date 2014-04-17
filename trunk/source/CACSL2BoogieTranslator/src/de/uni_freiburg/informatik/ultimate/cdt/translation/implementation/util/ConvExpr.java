package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;



/**
 * Provides static auxiliary methods for converting boogie expressions from one
 * type to another.
 * In boogie the operands and result of e.g., the "logical AND &&" are booleans, 
 * in C the operands and the result are of type int. We have to convert the
 * boogie expressions to a type that fits the boogie operators.
 * @author Matthias Heizmann
 */

public class ConvExpr {

	/**
	 * Convert Expression of some type to an expression of boolean type.
	 * If the expression expr
	 * <ul>
	 * <li> has type boolean we return expr
	 * <li> has type int we return <i>expr != 0</i>
	 * <li> has type real we return <i>expr != 0.0</i>
	 * <li> has type $Pointer$ we return <i>expr != #NULL</i>
	 * </ul> 
	 * Other types are not supported.
	 * If the expression was obtained by a conversion from bool to int, we try
	 * to get rid of the former conversion instead of applying a new one.
	 */
	public static RValue toBoolean(final ILocation loc, final RValue rVal) {
		assert !rVal.isBoogieBool;
		Expression resultEx = null;
		Expression e = rVal.getValue();
		if (e instanceof IntegerLiteral) {
			if (Integer.parseInt(((IntegerLiteral) e).getValue()) == 0)
				resultEx = new BooleanLiteral(loc, new InferredType(
						Type.Boolean), false);
			else
				resultEx = new BooleanLiteral(loc, new InferredType(
						Type.Boolean), true);
		} else {
			if (rVal.cType instanceof CPrimitive) {
				switch (((CPrimitive) rVal.cType).getGeneralType()) {
				case FLOATTYPE:
					resultEx = new BinaryExpression(loc, new InferredType(
							InferredType.Type.Boolean),
							BinaryExpression.Operator.COMPNEQ, e,
							new RealLiteral(loc, SFO.NR0F));
					break;
				case INTTYPE:
//					final Expression unwrappedInt =
//					unwrapInt2Boolean(e);
//					if (unwrappedInt != null) {
//						resultEx = unwrappedInt;
//					}
//					else {
						resultEx = new BinaryExpression(loc, new InferredType(
								InferredType.Type.Boolean),
								BinaryExpression.Operator.COMPNEQ, e,
								new IntegerLiteral(loc, SFO.NR0));
//					}
					break;
				case VOID:
					default:
				}
			} else if (rVal.cType instanceof CPointer) {
				resultEx = new BinaryExpression(loc, 
//						new InferredType(
//						InferredType.Type.Boolean),
						BinaryExpression.Operator.COMPNEQ, e,
						MemoryHandler.constructNullPointer(loc));
			} else {
				String msg = "Don't know the type of this expression. Line: "
						+ e.getLocation().getStartLine();
				throw new AssertionError(msg);
			}
		}
		return new RValue(resultEx, new CPrimitive(PRIMITIVE.INT), true);
	}

	public static RValue boolToInt(ILocation loc, RValue rVal) {
		assert rVal.isBoogieBool;
		return new RValue(
				new IfThenElseExpression(
						loc, rVal.getValue(), new IntegerLiteral(loc, "1"), new IntegerLiteral(loc, "0")),
					rVal.cType,
					false);
	}
	
	
	public static ResultExpression rexIntToBoolIfNecessary(ILocation loc, ResultExpression rl) {
		ResultExpression rlToBool = null;
		if (rl.lrVal.isBoogieBool) {
			rlToBool = rl;
		} else {
			rlToBool = new ResultExpression(ConvExpr.toBoolean(loc, (RValue) rl.lrVal));
			rlToBool.addAll(rl);
		}
		return rlToBool;
	}

	public static ResultExpression rexBoolToIntIfNecessary(ILocation loc, ResultExpression rl) {
		ResultExpression rlToInt = null;
		if (rl.lrVal.isBoogieBool) {
			rlToInt = new ResultExpression(ConvExpr.boolToInt(loc, (RValue) rl.lrVal));
			rlToInt.addAll(rl);
		} else {
			rlToInt = rl;
		}
		return rlToInt;
	}
}
