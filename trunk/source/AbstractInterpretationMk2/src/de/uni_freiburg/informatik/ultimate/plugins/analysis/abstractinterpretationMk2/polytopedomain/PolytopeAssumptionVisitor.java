package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import parma_polyhedra_library.Coefficient;
import parma_polyhedra_library.Constraint;
import parma_polyhedra_library.Linear_Expression;
import parma_polyhedra_library.Linear_Expression_Coefficient;
import parma_polyhedra_library.Linear_Expression_Sum;
import parma_polyhedra_library.Relation_Symbol;

/**
 * This walker is used by the polytope domain to manifest the implications of
 * any expression into a given polytope. Set the actual polytope with
 * prepare(...).
 * 
 * @author GROSS-JAN
 *
 */
public class PolytopeAssumptionVisitor {

	private final PolytopeExpressionVisitor mExpressionVisitor;

	protected final Logger mLogger;

	/**
	 * Constructor
	 * 
	 * @param logger
	 */
	public PolytopeAssumptionVisitor(PolytopeExpressionVisitor expressionVisitor, Logger logger) {
		mLogger = logger;
		mExpressionVisitor = expressionVisitor;
		// mStates = new ArrayList<PolytopeState>();
	}

	/**
	 * 
	 * @param expr
	 * @return
	 */
	public List<PolytopeState> applyAssumption(Expression expr, List<PolytopeState> states, boolean negate) {
		if (expr instanceof BinaryExpression) {
			BinaryExpression binExpr = (BinaryExpression) expr;
			BinaryExpression.Operator oper = binExpr.getOperator();

			/*
			 * The negations are always brought "inside" and handled there
			 */
			switch (oper) {
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICAND:
			case LOGICOR:

				// do each side if it is not a unary expression
				boolean applyLeft = binExpr.getLeft() instanceof BinaryExpression;
				boolean applyRight = binExpr.getRight() instanceof BinaryExpression;

				// AND: apply both sides
				// OR: apply on each side on a separate copy

				if (((oper == BinaryExpression.Operator.LOGICAND) && !negate)
						|| ((oper == BinaryExpression.Operator.LOGICOR) && negate)) {
					// a AND b
					// a NOR b = not(a) AND not(b)
					// do each side if it is not a unary expression
					if (applyLeft) {
						states = applyAssumption(binExpr.getLeft(), states, negate);
					}
					if (applyRight) {
						states = applyAssumption(binExpr.getRight(), states, negate);
					}
					return states;
				} else if ((oper == BinaryExpression.Operator.LOGICIMPLIES) && negate) {
					// a NIMPL b = a AND not(b)
					if (applyLeft) {
						states = applyAssumption(binExpr.getLeft(), states, false);
					}
					if (applyRight) {
						states = applyAssumption(binExpr.getRight(), states, true);
					}
					return states;
				} else if (((oper == BinaryExpression.Operator.LOGICAND) && negate)
						|| ((oper == BinaryExpression.Operator.LOGICOR) && !negate)) {
					// a NAND b = not(a) OR not(b)
					// a OR b

					// here is where the number of resulting states doubles
					List<PolytopeState> newStates = new ArrayList<PolytopeState>();

					// do each side if it is not a unary expression
					// apply the assumption result for left and right on two
					// copies
					if (applyLeft) {
						newStates.addAll(applyAssumption(binExpr.getLeft(), copyStatesIf(states, applyRight), negate));
					}
					if (applyRight) {
						newStates.addAll(applyAssumption(binExpr.getRight(), states, negate));
					}
					return newStates;
				} else if ((oper == BinaryExpression.Operator.LOGICIMPLIES) && !negate) {
					// a IMPL b = not(a) OR b
					// here is where the number of resulting states doubles
					List<PolytopeState> newStates = new ArrayList<PolytopeState>();

					if (applyLeft) {
						newStates.addAll(applyAssumption(binExpr.getLeft(), copyStatesIf(states, applyRight), true));
					}
					if (applyRight) {
						newStates.addAll(applyAssumption(binExpr.getRight(), states, false));
					}
					return newStates;
				} else if ((oper == BinaryExpression.Operator.LOGICIFF)) {
					// a IFF b = (a AND b) OR (not(a) AND not(b))
					// a NIFF b = (a AND not(b)) OR (not(a) AND b)

					// here is where the number of resulting states doubles
					List<PolytopeState> posStates = new ArrayList<PolytopeState>();

					// 'pos' (a AND b)
					posStates.addAll(applyAssumption(binExpr.getLeft(), copyStatesIf(states, true), true));
					posStates = applyAssumption(binExpr.getRight(), posStates, !negate);

					// 'neg' (not(a) AND not(b))
					states = applyAssumption(binExpr.getLeft(), states, false);
					states = applyAssumption(binExpr.getRight(), states, negate);

					states.addAll(posStates);

					return states;
				}
				break;

			default:
				// == Relations ===
				// check the type
				// with integers "x > c" is realized as "x >= c + 1"
				boolean integer = false;
				IType typeLeft = binExpr.getLeft().getType();
				IType typeRight = binExpr.getRight().getType();

				if (typeLeft instanceof ArrayType) {
					typeLeft = ((ArrayType) typeLeft).getValueType();
				}
				if (typeRight instanceof ArrayType) {
					typeRight = ((ArrayType) typeRight).getValueType();
				}

				if (typeLeft instanceof PrimitiveType && typeRight instanceof PrimitiveType) {
					PrimitiveType ptLeft = (PrimitiveType) typeLeft;
					PrimitiveType ptRight = (PrimitiveType) typeRight;
					integer = ptLeft.getTypeCode() == PrimitiveType.INT && ptRight.getTypeCode() == PrimitiveType.INT;
				} else {
					// handle this type of type
					throw new UnsupportedOperationException(
							"We do not support expressions like this: " + BoogiePrettyPrinter.print(expr));
				}

				List<PolytopeState> newStates = new ArrayList<PolytopeState>();
				boolean applied = true;
				for (PolytopeState state : states) {
					// evaluate both sides first
					mExpressionVisitor.prepare(state, "");
					Linear_Expression left = mExpressionVisitor.walk(binExpr.getLeft());
					Linear_Expression right = mExpressionVisitor.walk(binExpr.getRight());

					if (left == null || right == null) {
						// the resulting expression is top
						// mLogger.warn(String.format("Cannot linearize
						// expression \"%s\"",
						// expr));
						continue;
					}

					Linear_Expression rightPlusOne = new Linear_Expression_Sum(right,
							new Linear_Expression_Coefficient(new Coefficient(1)));
					Linear_Expression leftPlusOne = new Linear_Expression_Sum(left,
							new Linear_Expression_Coefficient(new Coefficient(1)));

					if (oper == BinaryExpression.Operator.COMPEQ && negate
							|| oper == BinaryExpression.Operator.COMPNEQ && !negate) {

						// left != right (NOT_EQUAL operator is broken)
						// make two constraints out of it, since the
						// and connect it with OR
						PolytopeState copy = state.copy().getConcrete();

						if (integer) {
							state.addConstraint(new Constraint(left, Relation_Symbol.GREATER_OR_EQUAL, rightPlusOne));
							copy.addConstraint(new Constraint(leftPlusOne, Relation_Symbol.LESS_OR_EQUAL, right));
						} else {
							state.addConstraint(new Constraint(left, Relation_Symbol.GREATER_THAN, right));
							copy.addConstraint(new Constraint(left, Relation_Symbol.LESS_THAN, right));
						}

						newStates.add(copy);
					} else if (oper == BinaryExpression.Operator.COMPEQ && !negate
							|| oper == BinaryExpression.Operator.COMPNEQ && negate) {
						state.addConstraint(new Constraint(left, Relation_Symbol.EQUAL, right));
					} else if (oper == BinaryExpression.Operator.COMPGEQ && !negate
							|| oper == BinaryExpression.Operator.COMPLT && negate) {
						state.addConstraint(new Constraint(left, Relation_Symbol.GREATER_OR_EQUAL, right));
					} else if (oper == BinaryExpression.Operator.COMPLEQ && !negate
							|| oper == BinaryExpression.Operator.COMPGT && negate) {
						state.addConstraint(new Constraint(left, Relation_Symbol.LESS_OR_EQUAL, right));
					} else if (oper == BinaryExpression.Operator.COMPLT && !negate
							|| oper == BinaryExpression.Operator.COMPGEQ && negate) {
						if (integer) {
							state.addConstraint(new Constraint(leftPlusOne, Relation_Symbol.LESS_OR_EQUAL, right));
						} else {
							state.addConstraint(new Constraint(left, Relation_Symbol.LESS_THAN, right));
						}
					} else if (oper == BinaryExpression.Operator.COMPGT && !negate
							|| oper == BinaryExpression.Operator.COMPLEQ && negate) {
						if (integer) {
							state.addConstraint(new Constraint(left, Relation_Symbol.GREATER_OR_EQUAL, rightPlusOne));
						} else {
							state.addConstraint(new Constraint(left, Relation_Symbol.GREATER_THAN, right));
						}
					} else {
						applied = false; // not handeled relation symbol
						break;
					}
				}
				states.addAll(newStates);
				if (applied) {
					return states;
				}
			} // switch
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unaryExpression = (UnaryExpression) expr;
			if (unaryExpression.getOperator() == UnaryExpression.Operator.LOGICNEG) {
				return applyAssumption(unaryExpression.getExpr(), states, !negate);
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (expr instanceof BooleanLiteral) {
			BooleanLiteral boolFormula = (BooleanLiteral) expr;
			if (boolFormula.getValue() != negate) {
				// "assume true;" or "assume !false;" -> nothing to narrow
				return states;
			} else {
				// "assume false;" or "assume !true";
				// return createBottom();
				return new ArrayList<PolytopeState>();
			}
		}

		// mLogger.warn(String.format("Can not reduce value range at assume
		// statement \"%s\"",
		// expr));
		return states;
	}

	/**
	 * create a copy only if needed
	 *
	 * @param states
	 * @param copy
	 * @return
	 */
	protected List<PolytopeState> copyStatesIf(List<PolytopeState> states, boolean copy) {
		if (!copy) {
			return states;
		}

		List<PolytopeState> copyStates;
		copyStates = new ArrayList<PolytopeState>();
		for (PolytopeState state : states) {
			copyStates.add(state.copy().getConcrete());
		}
		return copyStates;
	}
}
