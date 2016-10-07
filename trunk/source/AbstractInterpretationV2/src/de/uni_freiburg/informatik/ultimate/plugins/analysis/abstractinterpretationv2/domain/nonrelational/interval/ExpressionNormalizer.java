/*
 * Copyright (C) 2015-2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.NormalFormTransformer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExpressionNormalizer extends BoogieTransformer {

	private final NormalFormTransformer<Expression> mNormalFormTransformer;

	ExpressionNormalizer() {
		mNormalFormTransformer = new NormalFormTransformer<>(new BoogieExpressionTransformer());
	}

	public Expression transform(final Expression expr) {
		return processExpression(expr);
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		if (expr instanceof BinaryExpression) {
			return postNormalize(expr, normalizeBinaryExpression((BinaryExpression) expr));
		} else if (expr instanceof UnaryExpression) {
			return postNormalize(expr, normalizeUnaryExpression((UnaryExpression) expr));
		}
		return super.processExpression(expr);
	}

	private Expression normalizeBinaryExpression(final BinaryExpression expr) {
		System.out.println(BoogiePrettyPrinter.print(expr));
		final Operator operator = expr.getOperator();
		final Expression right = processExpression(expr.getRight());
		final Expression left = processExpression(expr.getLeft());
		if (operator == Operator.COMPNEQ) {
			if (isPrimitive(expr)) {
				final PrimitiveType prim = (PrimitiveType) expr.getType();
				final PrimitiveType leftPrim = (PrimitiveType) left.getType();
				final PrimitiveType rightPrim = (PrimitiveType) right.getType();
				if (isOfType(PrimitiveType.BOOL, prim, leftPrim, rightPrim)) {
					final Expression negatedRight = not(expr, right);
					// x != y ---> x == !y
					return createBinaryExpr(expr, Operator.COMPEQ, left, negatedRight);
				}
			}
			final Expression negativeCase = createBinaryExpr(expr, Operator.COMPLT, left, right);
			final Expression positiveCase = createBinaryExpr(expr, Operator.COMPGT, left, right);
			return or(expr, negativeCase, positiveCase);
		} else if (operator == Operator.COMPGT || operator == Operator.COMPLT) {
			if (isPrimitive(expr)) {
				final PrimitiveType primLeft = (PrimitiveType) left.getType();
				final PrimitiveType primRight = (PrimitiveType) right.getType();

				if (isOfType(PrimitiveType.INT, primLeft, primRight)) {
					if (operator == Operator.COMPGT) {
						// x > y ---> x >= y + 1
						final Expression newRightGt =
								createBinaryExpr(right, Operator.ARITHPLUS, right, createIntegerLiteral(right, "1"));
						return createBinaryExpr(expr, Operator.COMPGEQ, left, newRightGt);

					} else if (operator == Operator.COMPLT) {
						// x < y ---> x <= y - 1
						final BinaryExpression newRightLt = new BinaryExpression(right.getLocation(), right.getType(),
								Operator.ARITHMINUS, right, createIntegerLiteral(right, "1"));
						return createBinaryExpr(expr, Operator.COMPLEQ, left, newRightLt);
					}
				}
			}
		} else if (operator == Operator.LOGICIMPLIES) {
			// x ==> y ---> !x || y
			return createBinaryExpr(expr, Operator.LOGICOR, not(expr, left), right);
		} else if (operator == Operator.LOGICIFF) {
			// a <==> b ---> a && b || !a && !b
			final Expression newTrueExpression = and(expr, right, left);
			final Expression newFalseExpression = and(expr, not(expr, right), not(expr, left));
			return or(expr, newTrueExpression, newFalseExpression);
		} else if (operator == Operator.ARITHPLUS || operator == Operator.ARITHMINUS) {
			if (right instanceof UnaryExpression) {
				final UnaryExpression uRight = (UnaryExpression) right;
				if (uRight.getOperator() == UnaryExpression.Operator.ARITHNEGATIVE) {
					// x + -y ---> x - y
					// x - -y ---> x + y
					return createBinaryExpr(expr,
							operator == Operator.ARITHPLUS ? Operator.ARITHMINUS : Operator.ARITHPLUS, left,
							uRight.getExpr());
				}
			}

			if (left instanceof UnaryExpression) {
				final UnaryExpression uLeft = (UnaryExpression) left;
				if (operator == Operator.ARITHPLUS && uLeft.getOperator() == UnaryExpression.Operator.ARITHNEGATIVE) {
					// -x + y ---> y - x
					return createBinaryExpr(expr, Operator.ARITHMINUS, right, uLeft.getExpr());
				}

				if (uLeft.getOperator() == UnaryExpression.Operator.ARITHNEGATIVE
						&& right instanceof IdentifierExpression) {
					final IdentifierExpression idRight = (IdentifierExpression) right;
					if (uLeft.getExpr() instanceof IdentifierExpression) {
						final IdentifierExpression innerIdLeft = (IdentifierExpression) uLeft.getExpr();
						if (innerIdLeft.getIdentifier().equals(idRight.getIdentifier())) {
							// -x - x ==> -2x
							return createBinaryExpr(expr, Operator.ARITHMUL, neg(expr, createIntegerLiteral(expr, "2")),
									idRight);
						}
					}
				}
			}

			if (left instanceof IdentifierExpression && right instanceof IdentifierExpression) {
				final IdentifierExpression idLeft = (IdentifierExpression) left;
				final IdentifierExpression idRight = (IdentifierExpression) right;

				if (idLeft.getIdentifier().equals(idRight.getIdentifier())) {
					// x - x ==> 0
					// x + x ==> 2x
					return (operator == Operator.ARITHPLUS
							? createBinaryExpr(expr, Operator.ARITHMUL, createIntegerLiteral(expr, "2"), idLeft)
							: createIntegerLiteral(expr, "0"));
				}
			}
		}

		if (left == expr.getLeft() && right == expr.getRight()) {
			// nothing changed
			return expr;
		}
		return createBinaryExpr(expr, expr.getOperator(), left, right);
	}

	private Expression normalizeUnaryExpression(final UnaryExpression expr) {
		System.out.println(BoogiePrettyPrinter.print(expr));
		final Expression left = processExpression(expr.getExpr());

		if (expr.getOperator() == UnaryExpression.Operator.LOGICNEG) {
			final Expression preNnf = createUnaryExpr(expr, expr.getOperator(), left);
			final Expression nnf = mNormalFormTransformer.rewriteNotEquals(preNnf);
			if (nnf != preNnf) {
				// nnf transformation had something to do
				return nnf;
			}
		}
		if (left == expr.getExpr()) {
			// nothing changed
			return expr;
		}
		return createUnaryExpr(expr, expr.getOperator(), left);
	}

	private static Expression or(final Expression oldExpr, final Expression left, final Expression right) {
		return createBinaryExpr(oldExpr, Operator.LOGICOR, left, right);
	}

	private static Expression not(final Expression oldExpr, final Expression left) {
		return createUnaryExpr(oldExpr, UnaryExpression.Operator.LOGICNEG, left);
	}

	private static Expression neg(final Expression oldExpr, final Expression left) {
		return createUnaryExpr(oldExpr, UnaryExpression.Operator.ARITHNEGATIVE, left);
	}

	private static Expression and(final Expression oldExpr, final Expression left, final Expression right) {
		return createBinaryExpr(oldExpr, Operator.LOGICAND, left, right);
	}

	private static IntegerLiteral createIntegerLiteral(final Expression old, final String value) {
		return new IntegerLiteral(old.getLocation(), BoogieType.TYPE_INT, value);
	}

	private static Expression createBinaryExpr(final Expression oldExpr, final Operator op, final Expression left,
			final Expression right) {
		return new BinaryExpression(oldExpr.getLocation(), getNewTypeBinary(op, left, right), op, left, right);
	}

	private static Expression createUnaryExpr(final Expression oldExpr, final UnaryExpression.Operator op,
			final Expression opper) {
		return new UnaryExpression(oldExpr.getLocation(), getNewTypeUnary(op, opper), op, opper);
	}

	private static IBoogieType getNewTypeBinary(final Operator op, final Expression left, final Expression right) {
		switch (op) {
		case ARITHDIV:
		case ARITHMINUS:
		case ARITHMOD:
		case ARITHMUL:
		case ARITHPLUS:
		case BITVECCONCAT:
			assert left.getType().equals(right.getType()) : "Type error";
			return left.getType();
		case COMPEQ:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPNEQ:
		case COMPPO:
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR:
			return BoogieType.TYPE_BOOL;
		default:
			throw new IllegalArgumentException("Unknown operator: " + op);
		}
	}

	private static IBoogieType getNewTypeUnary(final UnaryExpression.Operator op, final Expression opper) {
		switch (op) {
		case ARITHNEGATIVE:
			return opper.getType();
		case LOGICNEG:
			return BoogieType.TYPE_BOOL;
		case OLD:
			return opper.getType();
		default:
			throw new IllegalArgumentException("Unknown operator: " + op);
		}
	}

	private static boolean isPrimitive(final BinaryExpression expr) {
		return expr.getType() instanceof PrimitiveType && expr.getLeft().getType() instanceof PrimitiveType
				&& expr.getRight().getType() instanceof PrimitiveType;
	}

	private static boolean isOfType(final int typecode, final PrimitiveType... primitiveTypes) {
		if (primitiveTypes == null || primitiveTypes.length == 0) {
			return false;
		}
		return Arrays.stream(primitiveTypes).allMatch(a -> a.getTypeCode() == typecode);
	}

	private Expression postNormalize(final Expression oldExpr, final Expression newExpr) {
		if (newExpr == null || newExpr == oldExpr) {
			return oldExpr;
		}
		ModelUtils.copyAnnotations(oldExpr, newExpr);
		return processExpression(newExpr);
	}
}
