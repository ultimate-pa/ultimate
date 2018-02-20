package de.uni_freiburg.informatik.ultimate.boogie.typechecker;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;

public class TypeCheckHelper {

	public static <T> BoogieType typeCheckArrayAccessExpressionOrLhs(final BoogieType arrayType,
				final List<BoogieType> indicesTypes,
				final ITypeErrorReporter<T> typeErrorReporter) {
			BoogieType resultType;
			if (!(arrayType instanceof BoogieArrayType)) {
				if (!arrayType.equals(BoogieType.TYPE_ERROR)) {
					typeErrorReporter.report(exp -> "Type check failed (not an array): " + exp);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final BoogieArrayType arr = (BoogieArrayType) arrayType;
				final BoogieType[] subst = new BoogieType[arr.getNumPlaceholders()];
				if (indicesTypes.size() != arr.getIndexCount()) {
					typeErrorReporter.report(exp -> "Type check failed (wrong number of indices): " + exp);
				} else {
					for (int i = 0; i < indicesTypes.size(); i++) {
						final BoogieType t = indicesTypes.get(i);
						if (!t.equals(BoogieType.TYPE_ERROR) && !arr.getIndexType(i).unify(t, subst)) {
							final int index = i;
							typeErrorReporter.report(exp -> "Type check failed (index " + index + "): " + exp);
						}
					}
				}
				resultType = arr.getValueType().substitutePlaceholders(subst);
			}
			return resultType;
		}

	public static <T> BoogieType typeCheckStructAccessExpressionOrLhs(final BoogieType structType, final String accessedField,
				final ITypeErrorReporter<T> typeErrorReporter) {
			BoogieType resultType;
			if (!(structType instanceof BoogieStructType)) {
				if (!structType.equals(BoogieType.TYPE_ERROR)) {
					typeErrorReporter.report(exp -> "Type check failed (not a struct): " + exp);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final BoogieStructType str = (BoogieStructType) structType;
				resultType = null;
				for (int i = 0; i < str.getFieldCount(); i++) {
					if (str.getFieldIds()[i].equals(accessedField)) {
						resultType = str.getFieldType(i);
					}
				}
				if (resultType == null) {
					typeErrorReporter.report(exp -> "Type check failed (field " +
							((StructAccessExpression) exp).getField() + " not in struct): " + exp);
					resultType = BoogieType.TYPE_ERROR;
				}
			}
			return resultType;
		}

	public static <T> BoogieType typeCheckBitVectorAccessExpression(final int bvlen, int end, int start,
				final BoogieType bvType,
				final ITypeErrorReporter<T> typeErrorReporter) {
			BoogieType resultType;
			if (start < 0 || end < start || bvlen < end) {
				if (!bvType.equals(BoogieType.TYPE_ERROR)) {
					typeErrorReporter.report(exp -> "Type check failed for " + exp);
				}
				start = end = 0;
			}
			resultType = BoogieType.createBitvectorType(end - start);
			return resultType;
		}

	public static <T> BoogieType typeCheckUnaryExpression(final Operator op, final BoogieType subtype,
				final ITypeErrorReporter<T> typeErrorReporter) {
			BoogieType resultType;
			switch (op) {
			case LOGICNEG:
				if (!subtype.equals(BoogieType.TYPE_ERROR) && !subtype.equals(BoogieType.TYPE_BOOL)) {
					typeErrorReporter.report(exp -> "Type check failed for " + exp);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case ARITHNEGATIVE:
				if (!subtype.equals(BoogieType.TYPE_ERROR) && !subtype.equals(BoogieType.TYPE_INT)
						&& !subtype.equals(BoogieType.TYPE_REAL)) {
					typeErrorReporter.report(exp -> "Type check failed for " + exp);
				}
				resultType = subtype;
				break;
			case OLD:
				resultType = subtype;
				break;
			default:
				internalError("Unknown Unary operator " + op);
				resultType = BoogieType.TYPE_ERROR;
				break;
			}
			return resultType;
		}
	public static <T> BoogieType typeCheckBinaryExpression(final BinaryExpression.Operator op,
				final BoogieType leftType, final BoogieType rightType,
				final ITypeErrorReporter<T> typeErrorReporter) {
			BoogieType resultType;
			BoogieType left = leftType;
			BoogieType right = rightType;

			switch (op) {
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICAND:
			case LOGICOR:
				if (!left.equals(BoogieType.TYPE_ERROR) && !left.equals(BoogieType.TYPE_BOOL)
						|| !right.equals(BoogieType.TYPE_ERROR) && !right.equals(BoogieType.TYPE_BOOL)) {
					typeErrorReporter.report(binexp -> "Type check failed for " + binexp);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case ARITHDIV:
			case ARITHMINUS:
			case ARITHMOD:
			case ARITHMUL:
			case ARITHPLUS:
				/* Try to recover for error types */
				if (left.equals(BoogieType.TYPE_ERROR)) {
					left = right;
				} else if (right.equals(BoogieType.TYPE_ERROR)) {
					right = left;
				}
				if (!left.equals(right) || !left.equals(BoogieType.TYPE_INT) && !left.equals(BoogieType.TYPE_REAL)
						|| left.equals(BoogieType.TYPE_REAL)
								&& op == BinaryExpression.Operator.ARITHMOD) {
					typeErrorReporter.report(binexp -> "Type check failed for " + binexp);
					resultType = BoogieType.TYPE_ERROR;
				} else {
					resultType = left;
				}
				break;
			case COMPLT:
			case COMPGT:
			case COMPLEQ:
			case COMPGEQ:
				/* Try to recover for error types */
				if (left.equals(BoogieType.TYPE_ERROR)) {
					left = right;
				} else if (right.equals(BoogieType.TYPE_ERROR)) {
					right = left;
				}
				if (!left.equals(right) || !left.equals(BoogieType.TYPE_INT) && !left.equals(BoogieType.TYPE_REAL)) {
					typeErrorReporter.report(binexp -> "Type check failed for " + binexp);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case COMPNEQ:
			case COMPEQ:
				if (!left.isUnifiableTo(right)) {
					typeErrorReporter.report(binexp -> "Type check failed for " + binexp);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case COMPPO:
				if (!left.equals(right) && !left.equals(BoogieType.TYPE_ERROR)
						&& !right.equals(BoogieType.TYPE_ERROR)) {
					typeErrorReporter.report(
							binexp -> "Type check failed for " + binexp + ": " + leftType.getUnderlyingType() + " != "
											+ rightType.getUnderlyingType());
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case BITVECCONCAT:
				int leftLen = getBitVecLength(left);
				int rightLen = getBitVecLength(right);
				if (leftLen < 0 || rightLen < 0 || leftLen + rightLen < 0 /*
																			 * handle overflow
																			 */) {
					if (!left.equals(BoogieType.TYPE_ERROR) && !right.equals(BoogieType.TYPE_ERROR)) {
						typeErrorReporter.report(binexp -> "Type check failed for " + binexp);
					}
					leftLen = 0;
					rightLen = 0; /* recover */
				}
				resultType = BoogieType.createBitvectorType(leftLen + rightLen);
				break;
			default:
				internalError("Unknown Binary operator " + op);
				resultType = BoogieType.TYPE_ERROR;
				break;
			}
			return resultType;
		}

	public static void internalError(final String message) {
		throw new AssertionError(message);
	}

	public static int getBitVecLength(BoogieType t) {
		t = t.getUnderlyingType();
		if (!(t instanceof BoogiePrimitiveType)) {
			return -1;
		}
		return ((BoogiePrimitiveType) t).getTypeCode();
	}

	public static <T> BoogieType typeCheckArrayStoreExpression(final BoogieType arrayType,
				final List<BoogieType> indicesTypes, final BoogieType valueType,
				final ITypeErrorReporter<T> typeErrorReporter) {
			BoogieType resultType;
			if (!(arrayType instanceof BoogieArrayType)) {
				if (!arrayType.equals(BoogieType.TYPE_ERROR)) {
	//					typeError(expr, "Type check failed (not an array): " + expr);
					typeErrorReporter.report(exp -> "Type check failed (not an array): " + exp);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final BoogieArrayType arr = (BoogieArrayType) arrayType;
				final BoogieType[] subst = new BoogieType[arr.getNumPlaceholders()];
				if (indicesTypes.size() != arr.getIndexCount()) {
	//					typeError(expr, "Type check failed (wrong number of indices): " + expr);
					typeErrorReporter.report(exp -> "Type check failed (wrong number of indices): " + exp);
				} else {
					for (int i = 0; i < indicesTypes.size(); i++) {
	//						final BoogieType t = typecheckExpression(indices[i]);
						final BoogieType t = indicesTypes.get(i);//typecheckExpression(indices[i]);
						if (!t.equals(BoogieType.TYPE_ERROR) && !arr.getIndexType(i).unify(t, subst)) {
	//							typeError(expr, "Type check failed (index " + i + "): " + expr);
							final int index = i;
							typeErrorReporter.report(exp -> "Type check failed (index " + index + "): " + exp);
						}
					}
					if (!valueType.equals(BoogieType.TYPE_ERROR) && !arr.getValueType().unify(valueType, subst)) {
	//						typeError(expr, "Type check failed (value): " + expr);
						typeErrorReporter.report(exp -> "Type check failed (value): " + exp);
					}
				}
				resultType = arr;
			}
			return resultType;
		}

	public static String getLeftHandSideIdentifier(LeftHandSide lhs) {
		while (lhs instanceof ArrayLHS || lhs instanceof StructLHS) {
			if (lhs instanceof ArrayLHS) {
				lhs = ((ArrayLHS) lhs).getArray();
			} else if (lhs instanceof StructLHS) {
				lhs = ((StructLHS) lhs).getStruct();
			}
		}
		return ((VariableLHS) lhs).getIdentifier();
	}

	public static <T> void typeCheckAssignStatement(final String[] lhsIds, final BoogieType[] lhsTypes,
				final BoogieType[] rhsTypes, final ITypeErrorReporter<T> typeErrorReporter) {
			//			if (lhs.length != rhs.length) {
			if (lhsTypes.length != rhsTypes.length) {
	//				typeError(statement, "Number of variables do not match in " + statement);
				typeErrorReporter.report(stm -> "Number of variables do not match in " + stm);
			} else {
				for (int i = 0; i < lhsTypes.length; i++) {
	//					lhsId[i] = getLeftHandSideIdentifier(lhs[i]);
					for (int j = 0; j < i; j++) {
						if (lhsIds[i].equals(lhsIds[j])) {
	//							typeError(statement, "Variable appears multiple times in assignment: " + statement);
							typeErrorReporter.report(stm -> "Variable appears multiple times in assignment: " + stm);
						}
					}
					final BoogieType lhsType = lhsTypes[i];//typecheckLeftHandSide(lhs[i]);
					final BoogieType rhsType = rhsTypes[i];//typecheckExpression(rhs[i]);
					if (!lhsType.equals(BoogieType.TYPE_ERROR) && !rhsType.equals(BoogieType.TYPE_ERROR)
							&& !lhsType.equals(rhsType)) {
	//						typeError(statement, "Type mismatch (" + lhsType + " != " + rhsType + ") in " + statement);
						typeErrorReporter.report(stm ->
							"Type mismatch (" + lhsType + " != " + rhsType + ") in " + stm);
					}
				}
			}
		}

}
