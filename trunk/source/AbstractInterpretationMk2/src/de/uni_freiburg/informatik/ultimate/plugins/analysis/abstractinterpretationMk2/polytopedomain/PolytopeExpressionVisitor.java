package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util.ExpressionWalker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util.IExpressionVisitor;
import parma_polyhedra_library.Coefficient;
import parma_polyhedra_library.Constraint;
import parma_polyhedra_library.Linear_Expression;
import parma_polyhedra_library.Linear_Expression_Coefficient;
import parma_polyhedra_library.Linear_Expression_Difference;
import parma_polyhedra_library.Linear_Expression_Sum;
import parma_polyhedra_library.Linear_Expression_Times;
import parma_polyhedra_library.Linear_Expression_Unary_Minus;
import parma_polyhedra_library.Linear_Expression_Variable;
import parma_polyhedra_library.Relation_Symbol;
import parma_polyhedra_library.Variable;

/**
 * This walker does walk along boogie expressions and returns parma polyhedron
 * expressions. Top is represented by returning null. So if null is returned, we
 * say, we do not know anything about the expression (top)
 * 
 * @author Jan Hättig
 *
 */
public class PolytopeExpressionVisitor extends ExpressionWalker<Linear_Expression>
		implements IExpressionVisitor<Linear_Expression> {
	/**
	 * The actual state.
	 */
	protected PolytopeState mCurrentState;

	/**
	 * Logger object
	 */
	protected final Logger mLogger;

	/**
	 * Will be added to each identifier.
	 */
	protected String mPrefix;

	/**
	 * Constructor
	 * 
	 * @param logger
	 */
	public PolytopeExpressionVisitor(Logger logger) {
		mExpressionVisitor = this;
		mLogger = logger;
	}

	/**
	 * Sets the current state and prepares walking through an expression.
	 * Walking an expression does modify the given state
	 * 
	 * @param state
	 */
	public void prepare(PolytopeState state, String prefix) {
		mCurrentState = state;
		mPrefix = prefix;
	}

	@Override
	public void visitExpression(Expression expr) {
	}

	@Override
	public void visitedExpression(Expression expr, Linear_Expression result) {
	}

	@Override
	public Linear_Expression visit(ArrayAccessExpression expr) {
		// TODO: Do something better with the array
		// like using a polyhedron as value representation

		Expression array = expr.getArray();
		if (array instanceof IdentifierExpression) {
			IdentifierExpression arrayIdent = (IdentifierExpression) array;
			IType type = ((ArrayType) arrayIdent.getType()).getValueType();
			TypedAbstractVariable abst = new TypedAbstractVariable(arrayIdent.getIdentifier(),
					arrayIdent.getDeclarationInformation(), type);
			if (!mCurrentState.hasVariable(abst)) {
				mLogger.warn("Variable " + abst.toString() + " was not found in state " + mCurrentState.toString());
				mCurrentState.declareVariable(abst);
			}
			Variable variable = mCurrentState.getVariable(abst);

			return new Linear_Expression_Variable(variable);
		} else {
			return null;
		}
	}

	@Override
	public Linear_Expression visit(ArrayStoreExpression expr) {
		throw new RuntimeException("This visitor must only be called for pure right hand side expressions");
	}

	@Override
	protected Linear_Expression visit(BinaryExpression expr) {
		// evaluate both sides first and call the visiting function
		// override this to manipulate the walk-first behavior
		// override or extend visit(expr, left, right) to only change
		// the behavior for the evaluated epressions
		Linear_Expression left = walk(expr.getLeft());
		Linear_Expression right = walk(expr.getRight());
		return visit(expr, left, right);
	}

	@Override
	public Linear_Expression visit(BinaryExpression expr, Linear_Expression left, Linear_Expression right) {
		BinaryExpression.Operator op = expr.getOperator();
		switch (op) {
		case ARITHMUL:
			// we can only make linear expressions, otherwise we do not know
			if (left == null || right == null) {
				//propagate top
				return null;
			} else if (left instanceof Linear_Expression_Coefficient) {
				Linear_Expression_Coefficient leftCoef = (Linear_Expression_Coefficient) left;
				if (leftCoef.is_zero() || (right instanceof Linear_Expression_Coefficient
						&& ((Linear_Expression_Coefficient) right).is_zero())) {
					// return 0 if one side is 0
					return new Linear_Expression_Coefficient(new Coefficient(0));
				} else if (right instanceof Linear_Expression_Variable) {
					Linear_Expression_Variable rightVar = (Linear_Expression_Variable) right;
					return new Linear_Expression_Times(leftCoef.argument(), rightVar.argument());
				} else {
					return new Linear_Expression_Times(leftCoef.argument(), right);
				}
			} else if (right instanceof Linear_Expression_Coefficient) {
				Linear_Expression_Coefficient rightCoef = (Linear_Expression_Coefficient) right;
				if (rightCoef.is_zero()) {
					// return 0 if one side is 0
					return new Linear_Expression_Coefficient(new Coefficient(0));
				} else if (left instanceof Linear_Expression_Variable) {
					Linear_Expression_Variable leftVar = (Linear_Expression_Variable) left;
					// arguments may be switched in this case
					return new Linear_Expression_Times(rightCoef.argument(), leftVar.argument());
				} else {
					return new Linear_Expression_Times(left, rightCoef.argument());
				}
			} else {
				return null;
			}

		case ARITHPLUS:
			if (left == null || right == null) {
				return null; // bottom
			}
			return new Linear_Expression_Sum(left, right);

		case ARITHMINUS:
			if (left == null || right == null) {
				return null; // bottom
			}
			return new Linear_Expression_Difference(left, right);

		case ARITHDIV:
			if (left != null && left instanceof Linear_Expression_Coefficient
					&& ((Linear_Expression_Coefficient) left).is_zero()) {
				return new Linear_Expression_Coefficient(new Coefficient(0));
			} else if (left == null || right == null) {
				return null; // top
			} else if (right instanceof Linear_Expression_Coefficient && left instanceof Linear_Expression_Coefficient
					&& ((Linear_Expression_Coefficient) left).argument().getBigInteger()
							.compareTo(((Linear_Expression_Coefficient) right).argument().getBigInteger()) == 0) {
				return new Linear_Expression_Coefficient(new Coefficient(1));
			}
			return null;

		case ARITHMOD:
			if (left != null && left instanceof Linear_Expression_Coefficient
					&& ((Linear_Expression_Coefficient) left).is_zero()) {
				return new Linear_Expression_Coefficient(new Coefficient(0));
			} else {
				return null;
			}
		case BITVECCONCAT:
			return null;

		// logical junctions are not handled here, only boolean
		// operations

		case LOGICAND:
			// X and Y == x *s y

			if (left == null || right == null) {
				return null; // top
			} else if (left instanceof Linear_Expression_Coefficient) {
				Linear_Expression_Coefficient coLeft = (Linear_Expression_Coefficient) left;
				return new Linear_Expression_Times(coLeft.argument(), right);
			}

			if (right instanceof Linear_Expression_Coefficient) {
				Linear_Expression_Coefficient coRight = (Linear_Expression_Coefficient) right;
				return new Linear_Expression_Times(left, coRight.argument());
			}
			return null;

		case LOGICOR:
			// X or Y == x + y
			if (left == null || right == null) {
				return null; // top
			} else {
				return new Linear_Expression_Sum(left, right);
			}

		case LOGICIMPLIES:
			// X -> Y == not(X) OR Y == (1 - x) + y
			if (left == null || right == null) {
				return null; // top
			} else {
				return new Linear_Expression_Sum(
						new Linear_Expression_Difference(new Linear_Expression_Coefficient(new Coefficient(1)), left),
						right);
			}

		case COMPGEQ:
		case COMPGT:
		case COMPEQ:
		case COMPLEQ:
		case COMPLT:
		case COMPNEQ:
		case COMPPO:
			if (left == null || right == null) {
				return null; // an expression which we cannot
								// represent
			}
			// check the state, check whether the assumption can be
			// true
			Relation_Symbol rel = null;
			switch (op) {
			case COMPEQ:
				rel = Relation_Symbol.EQUAL;
				break;
			case COMPNEQ:
				rel = Relation_Symbol.NOT_EQUAL;
				break;
			case COMPGEQ:
				rel = Relation_Symbol.GREATER_OR_EQUAL;
				break;
			case COMPGT:
				rel = Relation_Symbol.GREATER_THAN;
				break;
			case COMPLEQ:
				rel = Relation_Symbol.LESS_OR_EQUAL;
				break;
			case COMPLT:
				rel = Relation_Symbol.LESS_THAN;
				break;
			case COMPPO:
			default:
				throw new UnsupportedOperationException();
			}
			PolytopeState copy = mCurrentState.copy();
			copy.addConstraint(new Constraint(left, rel, right));
			if (copy.isBottom()) {
				// the expression is never true, always false
				return new Linear_Expression_Coefficient(new Coefficient(0));
			} else if (copy.isSuperOrEqual(mCurrentState)) {
				// if we cut nothing away from the copy
				// the expression cannot be false, is always true
				return new Linear_Expression_Coefficient(new Coefficient(1));
			} else {
				// we do not know
				return null; // top
			}

		default:
			throw new UnsupportedOperationException();

		}
	}

	@Override
	public Linear_Expression visit(BitvecLiteral expr) {
		return null;
	}

	@Override
	public Linear_Expression visit(BitVectorAccessExpression expr, Linear_Expression val, int start, int end) {
		return null;
	}

	@Override
	public Linear_Expression visit(BooleanLiteral expr) {
		return new Linear_Expression_Coefficient(new Coefficient(expr.getValue() ? 1 : 0));
	}

	@Override
	public Linear_Expression visit(IntegerLiteral expr) {
		return new Linear_Expression_Coefficient(new Coefficient(expr.getValue()));
	}

	@Override
	public Linear_Expression visit(RealLiteral expr) {
		return null; // TODO?
		// return new Linear_Expression_Coefficient(new
		// Coefficient(expr.getValue()));
	}

	@Override
	public Linear_Expression visit(StringLiteral expr) {
		return null;
	}

	@Override
	public Linear_Expression visit(IdentifierExpression expr) {
		String ident = mPrefix + expr.getIdentifier();
		AbstractVariable abst = new AbstractVariable(ident);
		if (!mCurrentState.hasVariable(abst)) {
			mLogger.warn("Variable " + abst.toString() + " was not found in state " + mCurrentState.toString());
			mCurrentState.declareVariable(
					new TypedAbstractVariable(ident, expr.getDeclarationInformation(), expr.getType()));
		}
		Variable variable = mCurrentState.getVariable(abst);

		return new Linear_Expression_Variable(variable);
	}

	@Override
	protected Linear_Expression visit(UnaryExpression expr) {
		Linear_Expression value = walk(expr.getExpr());

		if (value == null) {
			return null;
		}
		if (expr.getOperator() == Operator.ARITHNEGATIVE) {
			return new Linear_Expression_Unary_Minus(value);
		} else if (expr.getOperator() == Operator.LOGICNEG) {
			// not(X) -> 1 - x
			return new Linear_Expression_Difference(new Linear_Expression_Coefficient(new Coefficient(1)), value);
		}

		throw new UnsupportedOperationException();
	}

	@Override
	public Linear_Expression visit(UnaryExpression expr, Linear_Expression value) {
		// this may not be called (since visit(UnaryExpression(...) is
		// overridden)
		throw new RuntimeException();
	}

	@Override
	public Linear_Expression visit(FunctionApplication expr, List<Linear_Expression> args) {
		return null; // TODO: is this a case which can happen?
	}

	@Override
	public Linear_Expression visit(IfThenElseExpression expr, Linear_Expression ifValue, Linear_Expression thenValue,
			Linear_Expression elseValue) {
		return null; // TODO: is this a case which can happen?
	}
}
