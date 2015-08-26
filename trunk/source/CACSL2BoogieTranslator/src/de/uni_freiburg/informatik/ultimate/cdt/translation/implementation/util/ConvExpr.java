package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;



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
	public static RValue toBoolean(final ILocation loc, final RValue rVal, 
			AExpressionTranslation expressionTranslation) {
		assert !rVal.isBoogieBool;
		CType underlyingType = rVal.cType.getUnderlyingType();
		Expression resultEx = null;
		Expression e = rVal.getValue();
		if (e instanceof IntegerLiteral) {
			if (Integer.parseInt(((IntegerLiteral) e).getValue()) == 0)
				resultEx = new BooleanLiteral(loc,  false);
			else
				resultEx = new BooleanLiteral(loc, true);
		} else {
			if (underlyingType instanceof CPrimitive) {
				switch (((CPrimitive) underlyingType).getGeneralType()) {
				case FLOATTYPE:
					resultEx = new BinaryExpression(loc, 
							BinaryExpression.Operator.COMPNEQ, e,
							new RealLiteral(loc, SFO.NR0F));
					break;
				case INTTYPE:
					Expression zero = expressionTranslation.constructLiteralForIntegerType(loc, 
							(CPrimitive) underlyingType, BigInteger.ZERO);
					resultEx = new BinaryExpression(loc, 
							BinaryExpression.Operator.COMPNEQ, e, zero);
					break;
				case VOID:
					default:
				}
			} else if (underlyingType instanceof CPointer) {
				resultEx = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPNEQ, e,
						new IdentifierExpression(loc, SFO.NULL));
			} else if (underlyingType instanceof CEnum) {
				resultEx = new BinaryExpression(loc,
						BinaryExpression.Operator.COMPNEQ, e,
						new IntegerLiteral(loc, SFO.NR0));
			} else {
				String msg = "Don't know the type of this expression. Line: "
						+ e.getLocation().getStartLine();
				throw new AssertionError(msg);
			}
		}
		return new RValue(resultEx, new CPrimitive(PRIMITIVE.INT), true);
	}

	public static RValue boolToInt(ILocation loc, RValue rVal, 
			AExpressionTranslation expressionTranslation) {
		assert rVal.isBoogieBool;
		Expression one = expressionTranslation.constructLiteralForIntegerType(loc, 
				new CPrimitive(PRIMITIVE.INT), BigInteger.ONE);
		Expression zero = expressionTranslation.constructLiteralForIntegerType(loc, 
				new CPrimitive(PRIMITIVE.INT), BigInteger.ZERO);
		return new RValue(
				new IfThenElseExpression(loc, rVal.getValue(), one, zero), 
				rVal.cType, false);
	}
	
	/**
	 * int <code>x</code> of form <code>y ? 1 : 0</code> becomes
	 * <code>!y ? 1 : 0</code>
	/** int <code>x</code> becomes <code>x == 0 ? 1 : 0</code> */	
	public static ResultExpression rexIntToBoolIfNecessary(ILocation loc, ResultExpression rl, 
			AExpressionTranslation expressionTranslation) {
		ResultExpression rlToBool = null;
		if (rl.lrVal.isBoogieBool) {
			rlToBool = rl;
		} else {
			rlToBool = new ResultExpression(ConvExpr.toBoolean(loc, (RValue) rl.lrVal, expressionTranslation));
			rlToBool.addAll(rl);
		}
		return rlToBool;
	}

	/** boolean <code>p</code> becomes <code>!p ? 1 : 0</code> */
	public static ResultExpression rexBoolToIntIfNecessary(ILocation loc, ResultExpression rl, 
			AExpressionTranslation expressionTranslation) {
		ResultExpression rlToInt = null;
		if (rl.lrVal.isBoogieBool) {
			rlToInt = new ResultExpression(ConvExpr.boolToInt(loc, (RValue) rl.lrVal, expressionTranslation));
			rlToInt.addAll(rl);
		} else {
			rlToInt = rl;
		}
		return rlToInt;
	}
}
