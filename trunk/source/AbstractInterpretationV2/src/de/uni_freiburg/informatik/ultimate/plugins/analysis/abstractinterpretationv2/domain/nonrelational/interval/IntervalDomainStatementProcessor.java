/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalStatementProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainStatementProcessor
        extends NonrelationalStatementProcessor<IntervalDomainState, IntervalDomainValue> {

	protected IntervalDomainStatementProcessor(final ILogger logger, final BoogieSymbolTable boogieSymbolTable,
	        final Boogie2SmtSymbolTable bpl2SmtTable, final int maxParallelStates) {
		super(logger, boogieSymbolTable, bpl2SmtTable, maxParallelStates);
	}

	@Override
	protected void addEvaluators(ExpressionEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock> evaluator,
	        IEvaluatorFactory<IntervalDomainValue, IntervalDomainState, CodeBlock> evaluatorFactory, Expression expr) {
		super.addEvaluators(evaluator, evaluatorFactory, expr);

		if (expr instanceof ArrayStoreExpression) {
			evaluator.addEvaluator(evaluatorFactory.createSingletonValueTopEvaluator());
		} else if (expr instanceof ArrayAccessExpression) {
			evaluator.addEvaluator(evaluatorFactory.createSingletonValueTopEvaluator());
		}
	}

	@Override
	protected IEvaluatorFactory<IntervalDomainValue, IntervalDomainState, CodeBlock> createEvaluatorFactory(
	        final int maxParallelStates) {
		EvaluatorFactory.Function<String, IntervalDomainValue> valueExpressionEvaluatorCreator = (value, type) -> {
			return new IntervalDomainValue(new IntervalValue(value), new IntervalValue(value));
		};
		return new EvaluatorFactory<>(getLogger(), maxParallelStates, new IntervalValueFactory(),
		        valueExpressionEvaluatorCreator);
	}

	@Override
	protected Expression normalizeExpression(Expression expr) {
		if (expr instanceof BinaryExpression) {
			return normalizeBinaryExpression((BinaryExpression) expr);
		} else if (expr instanceof UnaryExpression) {
			return normalizeUnaryExpression((UnaryExpression) expr);
		}

		return super.normalizeExpression(expr);
	}

	private Expression normalizeBinaryExpression(final BinaryExpression expr) {
		final Operator operator = expr.getOperator();

		if (operator == Operator.COMPNEQ) {
			if (expr.getType() instanceof PrimitiveType && expr.getLeft().getType() instanceof PrimitiveType
			        && expr.getRight().getType() instanceof PrimitiveType) {
				final PrimitiveType prim = (PrimitiveType) expr.getType();
				final PrimitiveType leftPrim = (PrimitiveType) expr.getLeft().getType();
				final PrimitiveType rightPrim = (PrimitiveType) expr.getRight().getType();
				if (prim.getTypeCode() == PrimitiveType.BOOL && leftPrim.getTypeCode() == PrimitiveType.BOOL
				        && rightPrim.getTypeCode() == PrimitiveType.BOOL) {
					final UnaryExpression negatedRight = new UnaryExpression(expr.getLocation(),
					        expr.getRight().getType(), UnaryExpression.Operator.LOGICNEG, expr.getRight());
					final BinaryExpression newExp = new BinaryExpression(expr.getLocation(), expr.getType(),
					        Operator.COMPEQ, expr.getLeft(), negatedRight);

					return newExp;
				}
			}

			final BinaryExpression negativeCase = new BinaryExpression(expr.getLocation(), expr.getType(),
			        Operator.COMPLT, expr.getLeft(), expr.getRight());
			final BinaryExpression positiveCase = new BinaryExpression(expr.getLocation(), expr.getType(),
			        Operator.COMPGT, expr.getLeft(), expr.getRight());

			final Expression newExp = new BinaryExpression(expr.getLocation(), expr.getType(), Operator.LOGICOR,
			        negativeCase, positiveCase);

			return newExp;
		} else if (operator == Operator.COMPGT || operator == Operator.COMPLT) {
			if (expr.getLeft().getType() instanceof PrimitiveType
			        && expr.getRight().getType() instanceof PrimitiveType) {
				final PrimitiveType primLeft = (PrimitiveType) expr.getLeft().getType();
				final PrimitiveType primRight = (PrimitiveType) expr.getRight().getType();

				if (primLeft.getTypeCode() == PrimitiveType.INT && primRight.getTypeCode() == PrimitiveType.INT) {
					BinaryExpression newExp;

					switch (operator) {
					case COMPGT:
						final BinaryExpression newRightGt = new BinaryExpression(expr.getRight().getLocation(),
						        expr.getRight().getType(), Operator.ARITHPLUS, expr.getRight(),
						        new IntegerLiteral(expr.getRight().getLocation(), "1"));

						newExp = new BinaryExpression(expr.getLocation(), expr.getType(), Operator.COMPGEQ,
						        expr.getLeft(), newRightGt);
						break;
					case COMPLT:
						final BinaryExpression newRightLt = new BinaryExpression(expr.getRight().getLocation(),
						        expr.getRight().getType(), Operator.ARITHMINUS, expr.getRight(),
						        new IntegerLiteral(expr.getRight().getLocation(), "1"));

						newExp = new BinaryExpression(expr.getLocation(), expr.getType(), Operator.COMPLEQ,
						        expr.getLeft(), newRightLt);
						break;
					default:
						throw new UnsupportedOperationException("Unexpected operator: " + operator);
					}

					return newExp;
				}
			}
		} else if (operator == Operator.LOGICIMPLIES) {
			final UnaryExpression newLeft = new UnaryExpression(expr.getLocation(), expr.getLeft().getType(),
			        UnaryExpression.Operator.LOGICNEG, expr.getLeft());

			final BinaryExpression newExp = new BinaryExpression(expr.getLocation(), expr.getType(), Operator.LOGICOR,
			        newLeft, expr.getRight());
			return newExp;
		} else if (operator == Operator.LOGICIFF) {
			final BinaryExpression newTrueExpression = new BinaryExpression(expr.getLocation(), expr.getType(),
			        Operator.LOGICAND, expr.getLeft(), expr.getRight());

			final UnaryExpression negatedLeft = new UnaryExpression(expr.getLocation(), expr.getLeft().getType(),
			        UnaryExpression.Operator.LOGICNEG, expr.getLeft());
			final UnaryExpression negatedRight = new UnaryExpression(expr.getLocation(), expr.getRight().getType(),
			        UnaryExpression.Operator.LOGICNEG, expr.getRight());
			final BinaryExpression newFalseExpression = new BinaryExpression(expr.getLocation(), expr.getType(),
			        Operator.LOGICAND, negatedLeft, negatedRight);

			final BinaryExpression newExp = new BinaryExpression(expr.getLocation(), expr.getType(), Operator.LOGICOR,
			        newTrueExpression, newFalseExpression);
			return newExp;
		} else if (operator == Operator.ARITHPLUS || operator == Operator.ARITHMINUS) {

			// x + -y ==> x - y
			// x - -y ==> x + y
			if (expr.getRight() instanceof UnaryExpression) {
				final UnaryExpression rightHandExpression = (UnaryExpression) expr.getRight();
				if (rightHandExpression.getOperator() == UnaryExpression.Operator.ARITHNEGATIVE) {
					Operator newOperator;

					if (operator == Operator.ARITHPLUS) {
						newOperator = Operator.ARITHMINUS;
					} else if (operator == Operator.ARITHMINUS) {
						newOperator = Operator.ARITHPLUS;
					} else {
						newOperator = operator;
					}

					return new BinaryExpression(expr.getLocation(), newOperator, expr.getLeft(),
					        rightHandExpression.getExpr());
				}
			}

			// -x + y ==> y - x
			if (operator == Operator.ARITHPLUS && expr.getLeft() instanceof UnaryExpression
			        && ((UnaryExpression) expr.getLeft()).getOperator() == UnaryExpression.Operator.ARITHNEGATIVE) {
				return new BinaryExpression(expr.getLocation(), Operator.ARITHMINUS, expr.getRight(),
				        ((UnaryExpression) expr.getLeft()).getExpr());
			}

			// x - x ==> 0
			// x + x ==> 2x
			if (expr.getLeft() instanceof IdentifierExpression && expr.getRight() instanceof IdentifierExpression) {
				final IdentifierExpression left = (IdentifierExpression) expr.getLeft();
				final IdentifierExpression right = (IdentifierExpression) expr.getRight();

				if (left.getIdentifier().equals(right.getIdentifier())) {
					return (operator == Operator.ARITHPLUS
					        ? new BinaryExpression(expr.getLocation(), Operator.ARITHMUL,
					                new IntegerLiteral(expr.getLocation(), "2"), left)
					        : new IntegerLiteral(expr.getLocation(), "0"));
				}
			}

			// -x - x ==> -2x
			if (expr.getLeft() instanceof UnaryExpression
			        && ((UnaryExpression) expr.getLeft()).getOperator() == UnaryExpression.Operator.ARITHNEGATIVE
			        && expr.getRight() instanceof IdentifierExpression) {
				final UnaryExpression leftUnary = (UnaryExpression) expr.getLeft();
				final IdentifierExpression rightIdentifier = (IdentifierExpression) expr.getRight();
				if (leftUnary.getExpr() instanceof IdentifierExpression && ((IdentifierExpression) leftUnary.getExpr())
				        .getIdentifier().equals(rightIdentifier.getIdentifier())) {
					return new BinaryExpression(expr.getLocation(), Operator.ARITHMUL,
					        new UnaryExpression(expr.getLocation(), UnaryExpression.Operator.ARITHNEGATIVE,
					                new IntegerLiteral(expr.getLocation(), "2")),
					        rightIdentifier);
				}
			}
		}

		return expr;
	}

	private Expression normalizeUnaryExpression(final UnaryExpression expr) {
		if (expr.getOperator() == UnaryExpression.Operator.LOGICNEG) {
			if (expr.getExpr() instanceof BinaryExpression) {
				final BinaryExpression binexp = (BinaryExpression) expr.getExpr();

				Operator newOp;

				Expression newLeft = binexp.getLeft();
				final IBoogieType leftType = binexp.getLeft().getType();
				Expression newRight = binexp.getRight();
				final IBoogieType rightType = binexp.getRight().getType();

				switch (binexp.getOperator()) {
				case COMPEQ:
					newOp = Operator.COMPNEQ;
					break;
				case COMPNEQ:
					newOp = Operator.COMPEQ;
					break;
				case COMPGEQ:
					newOp = Operator.COMPLT;
					break;
				case COMPGT:
					newOp = Operator.COMPLEQ;
					break;
				case COMPLEQ:
					newOp = Operator.COMPGT;
					break;
				case COMPLT:
					newOp = Operator.COMPGEQ;
					break;
				case LOGICAND:
					newOp = Operator.LOGICOR;
					newLeft = new UnaryExpression(binexp.getLocation(), leftType, UnaryExpression.Operator.LOGICNEG,
					        newLeft);
					newRight = new UnaryExpression(binexp.getLocation(), rightType, UnaryExpression.Operator.LOGICNEG,
					        newRight);
					break;
				case LOGICOR:
					newOp = Operator.LOGICAND;
					newLeft = new UnaryExpression(binexp.getLocation(), leftType, UnaryExpression.Operator.LOGICNEG,
					        newLeft);
					newRight = new UnaryExpression(binexp.getLocation(), rightType, UnaryExpression.Operator.LOGICNEG,
					        newRight);
					break;
				case COMPPO:
					getLogger().warn("The comparison operator " + binexp.getOperator() + " is not yet supported.");
				default:
					newOp = binexp.getOperator();
					throw new UnsupportedOperationException("Fix me: " + binexp.getOperator());
				}

				final BinaryExpression newExp = new BinaryExpression(binexp.getLocation(), expr.getType(), newOp,
				        newLeft, newRight);

				return newExp;
			} else if (expr.getExpr() instanceof UnaryExpression) {
				final UnaryExpression unexp = (UnaryExpression) expr.getExpr();
				if (unexp.getOperator() == UnaryExpression.Operator.LOGICNEG) {
					return unexp.getExpr();
				}
			}
		}

		return expr;
	}

}
