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
//	public static Expression toBoolean(final ILocation loc, final Expression e) {
	private Expression toBoolean(final ILocation loc, final Expression e) {
		Expression result;
		if (e instanceof IntegerLiteral) {
			if (Integer.parseInt(((IntegerLiteral) e).getValue()) == 0)
				result = new BooleanLiteral(loc, new InferredType(
						Type.Boolean), false);
			else
				result = new BooleanLiteral(loc, new InferredType(
						Type.Boolean), true);
		} else {
			IType t = e.getType();
			if (t != null) {
				assert t instanceof InferredType;
				InferredType it = (InferredType) t;
				switch (it.getType()) {
				case Boolean:
					result = e;
					break;
				case Integer:
					/*
					 * try to unwrap formerly introduced
					 * if-then-else wrapper
					 */
//					final Expression unwrappedInt =
//					unwrapInt2Boolean(e);
//					if (unwrappedInt != null) {
//						result = unwrappedInt;
//					}
//					else {
						result = new BinaryExpression(loc, new InferredType(
								InferredType.Type.Boolean),
								BinaryExpression.Operator.COMPNEQ, e,
								new IntegerLiteral(loc, SFO.NR0));
//					}
					break;
				case Real:
					result = new BinaryExpression(loc, new InferredType(
							InferredType.Type.Boolean),
							BinaryExpression.Operator.COMPNEQ, e,
							new RealLiteral(loc, SFO.NR0F));
					break;
				case Pointer:
					result = new BinaryExpression(loc, new InferredType(
							InferredType.Type.Boolean),
							BinaryExpression.Operator.COMPNEQ, e,
							MemoryHandler.constructNullPointer(loc));
					break;
				case Unknown:
				default:
					String msg = "Don't know the type of this expression. Line: "
							+ e.getLocation().getStartLine();
					throw new AssertionError(msg);
					//                        Dispatcher.error(loc, SyntaxErrorType.TypeError,
					//                                msg);
				}
			} else {
				throw new AssertionError("unknown Boogie Type for " + e);
				//                String msg = "Don't know the type of this expression. Line: "
				//                        + e.getLocation().getStartLine();
				//                Dispatcher.error(loc, SyntaxErrorType.TypeError, msg);
			}
		}
		return result;
	}


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
				resultEx = new BinaryExpression(loc, new InferredType(
						InferredType.Type.Boolean),
						BinaryExpression.Operator.COMPNEQ, e,
						MemoryHandler.constructNullPointer(loc));
			} else {
				String msg = "Don't know the type of this expression. Line: "
						+ e.getLocation().getStartLine();
				throw new AssertionError(msg);
			}
		}
		return new RValue(resultEx, new CPrimitive(PRIMITIVE.INT), true, rVal.isPointer);
	}

	/**
	 * Tries to unwrap an expression that was wrapped before. That is, it checks
	 * whether a given integer expression is wrapped in an if-then-else
	 * expression or not.
	 */
//	public static Expression unwrapInt2Boolean(final Expression expr) {
//		if (expr instanceof IfThenElseExpression) {
//			final IfThenElseExpression iteEx = (IfThenElseExpression)expr;
//			final Expression thenPart = iteEx.getThenPart();
//			if ((thenPart instanceof IntegerLiteral) &&
//					(((IntegerLiteral)thenPart).getValue() == SFO.NR1)) {
//				final Expression elsePart = iteEx.getElsePart();
//				if ((elsePart instanceof IntegerLiteral) &&
//						(((IntegerLiteral)elsePart).getValue() == SFO.NR0)) {
//					return iteEx.getCondition();
//				}
//			}
//		}
//		return null;
//	}

	public static RValue boolToInt(ILocation loc, RValue rVal) {
		assert rVal.isBoogieBool;
		return new RValue(
				new IfThenElseExpression(
						loc, rVal.getValue(), new IntegerLiteral(loc, "1"), new IntegerLiteral(loc, "0")),
					rVal.cType,
					false,
					rVal.isPointer);
	}

	public static Expression doStrangeThings(ASTType type, Expression expr) {
		if (type != null && type instanceof ArrayType) {
			type = ((ArrayType) type).getValueType();
			throw new AssertionError("formerly did the following, "
					+ "Matthias does not understand this.");
			//  } else if (type != null && type instanceof ArrayType) {
			//  return convertArith2Boolean(loc,
			//              ((ArrayType) type).getValueType(), e);
			//}
		}
		return expr;
	}





}
