/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue;

/**
 * Used to evaluate boogie statements during abstract interpretation
 * 
 * @author Christopher Dillo
 */
public class AbstractInterpretationBoogieVisitor {
	
	/**
	 * States before and after evaluating a statement
	 */
	private AbstractState m_currentState, m_resultingState;
	
	/**
	 * Result value of evaluating an expression
	 */
	private IAbstractValue<?> m_resultValue;
	
	private Logger m_logger;
	
	private IAbstractDomainFactory<?> m_numberFactory;
	
	private BoolDomainFactory m_boolFactory;
	
	/**
	 * The identifier for an LHS expression
	 * TODO: what about arrays and structs?
	 */
	private String m_lhsIdentifier;
	
	/**
	 * Flag set when encountering a unary NOT operation as !(a comp b) needs to be calculated as (a !comp b)
	 */
	private boolean m_negate;
	private void setNegate() {
		m_negate = true;
	}
	private boolean doNegate() {
		if (m_negate) {
			m_negate = false;
			return true;
		}
		return false;
		}
	
	public AbstractInterpretationBoogieVisitor(Logger logger, IAbstractDomainFactory<?> numberFactory, BoolDomainFactory boolFactory) {
		m_logger = logger;
		m_numberFactory = numberFactory;
		m_boolFactory = boolFactory;
	}
	
	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * STATEMENTS
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
	
	/**
	 * Evaluates a statement with regards to a current state and returns a resulting state 
	 * @param statement The statement to evaluate
	 * @param currentState The current abstract program state
	 * @return The resulting abstract program state
	 */
	public AbstractState evaluateStatement(Statement statement, AbstractState currentState) {
		m_currentState = currentState;
		if (currentState == null) return null;
		m_resultingState = currentState.copy();
		
		if (statement instanceof ReturnStatement) {
			visit((ReturnStatement) statement);
		} else if (statement instanceof HavocStatement) {
			visit((HavocStatement) statement);
		} else if (statement instanceof CallStatement) {
			visit((CallStatement) statement);
		} else if (statement instanceof AssignmentStatement) {
			visit((AssignmentStatement) statement);
		} else if (statement instanceof AssumeStatement) {
			visit((AssumeStatement) statement);
		} else {
			throw new UnsupportedOperationException(String.format("Unsupported statement type %s", statement.getClass()));
		}
		
		return m_resultingState;
	}

	protected void visit(ReturnStatement statement) {
		// TODO: support! (pop stack?)
		m_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(HavocStatement statement) {
		LeftHandSide[] lhs = statement.getIdentifiers();
		for (int i = 0; i < lhs.length; i++) {
			evaluateLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			m_resultingState.writeValue(m_lhsIdentifier, m_numberFactory.makeTopValue());
			// TODO: Check type, generate abstract value of proper domain (int, bool...)
		}
	}

	protected void visit(CallStatement statement) {
		// TODO: support! (push stack?)
		m_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(AssignmentStatement statement) {
		LeftHandSide[] lhs = statement.getLhs();
		Expression[] rhs = statement.getRhs();
		
		if (lhs.length != rhs.length) {
			m_logger.warn(String.format("%s lhs and rhs size mismatch!", statement.getClass()));
			return;
		}

		for (int i = 0; i < lhs.length; i++) {
			evaluateLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			m_resultingState.writeValue(m_lhsIdentifier, evaluateExpression(rhs[i]));
		}
	}

	protected void visit(AssumeStatement statement) {
		IAbstractValue<?> formulaResult = evaluateExpression(statement.getFormula());

		if (formulaResult == null) {
			m_logger.warn(String.format("Evaluating statement failed, returned null: %s", statement));
			return;
		}
		
		if (m_boolFactory.makeFromAbstractValue(formulaResult).isFalse()) {
			// expression evaluates to false for all values, so there is no resulting state.
			m_resultingState = null;
			return;
		}
		
		// TODO: reconstruct variable values that pass through the formula, adjust resulting statement
	}

	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * LEFT-HAND-SIDES
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

	protected void evaluateLeftHandSide(LeftHandSide lhs) {
		if (lhs instanceof ArrayLHS) {
			visit((ArrayLHS) lhs);
		} else if (lhs instanceof StructLHS) {
			visit((StructLHS) lhs);
		} else if (lhs instanceof VariableLHS) {
			visit((VariableLHS) lhs);
		} else {
			throw new UnsupportedOperationException(String.format("Unsupported LeftHandSide type %s", lhs.getClass()));
		}
	}
	
	protected void visit(VariableLHS lhs) {
		m_lhsIdentifier = lhs.getIdentifier();
	}

	protected void visit(StructLHS lhs) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
	}

	protected void visit(ArrayLHS lhs) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
	}
	
	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * EXPRESSIONS
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
	
	/**
	 * Evaluates an expression and returns the resulting abstract value
	 * @param expr The expression to evaluate
	 * @return The resulting abstract value
	 */
	protected IAbstractValue<?> evaluateExpression(Expression expr) {
		IAbstractValue<?> backup = m_resultValue; // do not overwrite, but keep (m_resultValue is used by recursive calls of this function)
		m_resultValue = null;

		// evaluate and store result in m_resultValue:
		if (expr instanceof ArrayAccessExpression) {
			visit((ArrayAccessExpression) expr);
		} else if (expr instanceof ArrayStoreExpression) {
			visit((ArrayStoreExpression) expr);
		} else if (expr instanceof BinaryExpression) {
			visit((BinaryExpression) expr);
		} else if (expr instanceof BitvecLiteral) {
			visit((BitvecLiteral) expr);
		} else if (expr instanceof BitVectorAccessExpression) {
			visit((BitVectorAccessExpression) expr);
		} else if (expr instanceof BooleanLiteral) {
			visit((BooleanLiteral) expr);
		} else if (expr instanceof IdentifierExpression) {
			visit((IdentifierExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			visit((IntegerLiteral) expr);
		} else if (expr instanceof RealLiteral) {
			visit((RealLiteral) expr);
		} else if (expr instanceof StringLiteral) {
			visit((StringLiteral) expr);
		} else if (expr instanceof StructAccessExpression) {
			visit((StructAccessExpression) expr);
		} else if (expr instanceof StructConstructor) {
			visit((StructConstructor) expr);
		} else if (expr instanceof UnaryExpression) {
			visit((UnaryExpression) expr);
		} else {
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", expr.getClass()));
		}
		
		IAbstractValue<?> returnValue = m_resultValue;
		m_resultValue = backup; // restore result value
		return returnValue;
	}

	protected void visit(UnaryExpression expr) {
		switch (expr.getOperator()) {
		case ARITHNEGATIVE:
			m_resultValue = evaluateExpression(expr.getExpr());
			if (m_resultValue != null)
				m_resultValue = m_resultValue.negative();
			break;
		case LOGICNEG :
			setNegate();
			m_resultValue = evaluateExpression(expr.getExpr());
			break;
		case OLD :
			// TODO: trace back? keep reference in abstract state?
		default:
			// TODO: support!
			m_logger.warn(String.format("Unsupported %s operator: %s", expr.getClass(), expr.getOperator()));
		}
	}

	protected void visit(StructConstructor expr) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(StructAccessExpression expr) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(StringLiteral expr) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(RealLiteral expr) {
		m_resultValue = m_numberFactory.makeRealValue(expr.getValue());
	}

	protected void visit(IntegerLiteral expr) {
		m_resultValue = m_numberFactory.makeIntegerValue(expr.getValue());
	}

	protected void visit(IdentifierExpression expr) {
		m_resultValue = m_currentState.readValue(expr.getIdentifier());
	}

	protected void visit(BooleanLiteral expr) {
		// TODO: support!
		boolean val = expr.getValue();
		m_resultValue = m_boolFactory.makeBooleanValue(doNegate() ? !val : val);
	}

	protected void visit(BitVectorAccessExpression expr) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(BitvecLiteral expr) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(BinaryExpression expr) {
		boolean neg = doNegate();
		IAbstractValue<?> left, right;
		left = evaluateExpression(expr.getLeft());
		right = evaluateExpression(expr.getRight());
		if ((left == null) || (right == null)) {
			m_logger.warn(String.format("Encountered null values in an %s", expr.getClass()));
			m_resultValue = null;
			return;
		}
		switch (expr.getOperator()) {
		case COMPLT :
			m_resultValue = neg ? left.compareIsGreaterEqual(right) : left.compareIsLess(right);
			break;
		case COMPGT :
			m_resultValue = neg ? left.compareIsLessEqual(right) : left.compareIsGreater(right);
			break;
		case COMPLEQ :
			m_resultValue = neg ? left.compareIsGreater(right) : left.compareIsLessEqual(right);
			break;
		case COMPGEQ :
			m_resultValue = neg ? left.compareIsLess(right) : left.compareIsGreaterEqual(right);
			break;
		case COMPEQ :
			m_resultValue = neg ? left.compareIsNotEqual(right) : left.compareIsEqual(right);
			break;
		case COMPNEQ :
			m_resultValue = neg ? left.compareIsEqual(right) : left.compareIsNotEqual(right);
			break;
		case ARITHPLUS :
			m_resultValue = left.add(right);
			break;
		case ARITHMINUS :
			m_resultValue = left.subtract(right);
			break;
		case ARITHMUL :
			m_resultValue = left.multiply(right);
			break;
		case ARITHDIV :
			m_resultValue = left.divide(right);
			break;
		case ARITHMOD :
			m_resultValue = left.modulo(right);
			break;
		case LOGICIFF :
		case LOGICIMPLIES :
		case LOGICAND :
		case LOGICOR :
			BoolValue leftBool = m_boolFactory.makeFromAbstractValue(left);
			BoolValue rightBool = m_boolFactory.makeFromAbstractValue(right);
			BoolValue result;
			switch (expr.getOperator()) {
			case LOGICIFF :
				result = leftBool.logicIff(rightBool);
				break;
			case LOGICIMPLIES :
				result = leftBool.logicImplies(rightBool);
				break;
			case LOGICAND :
				result = leftBool.logicAnd(rightBool);
				break;
			case LOGICOR :
				result = leftBool.logicOr(rightBool);
				break;
			default :
				result = m_boolFactory.makeBottomValue();
			}
			m_resultValue = neg ? result.logicNot() : result;
			break;
		case COMPPO :
		case BITVECCONCAT :
		default :
			// TODO: support!
			m_logger.warn(String.format("Unsupported %s operator: %s", expr.getClass(), expr.getOperator()));
		}
		m_logger.debug(String.format("BinOp [%s] %s%s [%s] = [%s]", left, neg ? "NOT " : "", expr.getOperator(), right, m_resultValue));
	}

	protected void visit(ArrayStoreExpression expr) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(ArrayAccessExpression expr) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}
}
