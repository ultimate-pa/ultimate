/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.AbstractInterpreter;

/**
 * Used to evaluate boogie statements during abstract interpretation
 * 
 * @author Christopher Dillo
 */
public class AbstractInterpretationBoogieVisitor extends BoogieVisitor {
	
	/**
	 * States before and after evaluating a statement
	 */
	private AbstractState m_currentState, m_resultingState;
	
	/**
	 * Result value of evaluating an expression
	 */
	private IAbstractValue m_resultValue;
	
	/**
	 * The identifier for an LHS expression
	 * TODO: what about arrays and structs?
	 */
	private String m_lhsIdentifier;
	
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
		m_resultingState = currentState.copy();
		m_resultingState.setSourceStatement(statement);
		
		processStatement(statement);
		
		return m_resultingState;
	}

	protected void visit(WhileStatement statement) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(ReturnStatement statement) {
		// TODO: support! (pop stack?)
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(Label statement) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(IfStatement statement) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(HavocStatement statement) {
		LeftHandSide[] lhs = statement.getIdentifiers();
		for (int i = 0; i < lhs.length; i++) {
			processLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			m_resultingState.writeValue(m_lhsIdentifier, AbstractInterpreter.s_domainFactory.makeTopValue());
			// TODO: Check type, generate abstract value of proper domain (int, bool...)
		}
	}

	protected void visit(GotoStatement statement) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(CallStatement statement) {
		// TODO: support! (push stack?)
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(BreakStatement statement) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(AssignmentStatement statement) {
		LeftHandSide[] lhs = statement.getLhs();
		Expression[] rhs = statement.getRhs();
		
		if (lhs.length != rhs.length) {
			AbstractInterpreter.s_logger.warn(String.format("%s lhs and rhs size mismatch!", statement.getClass()));
			return;
		}

		for (int i = 0; i < lhs.length; i++) {
			processLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			m_resultingState.writeValue(m_lhsIdentifier, evaluateExpression(rhs[i]));
		}
	}

	protected void visit(AssumeStatement statement) {
		IAbstractValue formulaResult = evaluateExpression(statement.getFormula());
		
		if ((formulaResult == null) || (formulaResult.isBottom())) {
			// expression evaluates to false for all values, so there is no resulting state.
			m_resultingState = null;
			return;
		}
		
		// TODO: reconstruct variable values that pass through the formula, adjust resulting statement
	}

	protected void visit(AssertStatement statement) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * LEFT-HAND-SIDES
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

	protected void visit(VariableLHS lhs) {
		m_lhsIdentifier = lhs.getIdentifier();
	}

	protected void visit(StructLHS lhs) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
	}

	protected void visit(ArrayLHS lhs) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
	}
	
	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * EXPRESSIONS
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
	
	/**
	 * Evaluates an expression and returns the resulting abstract value
	 * @param expr The expression to evaluate
	 * @return The resulting abstract value
	 */
	protected IAbstractValue evaluateExpression(Expression expr) {
		IAbstractValue backup = m_resultValue; // do not overwrite, but keep (m_resultValue is used by recursive calls of this function)
		m_resultValue = null;
		
		processExpression(expr); // stores result in m_resultValue
		
		IAbstractValue returnValue = m_resultValue;
		m_resultValue = backup; // restore result value
		return returnValue;
	}

	protected void visit(WildcardExpression expr) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(UnaryExpression expr) {
		switch (expr.getOperator()) {
		case ARITHNEGATIVE:
			m_resultValue = evaluateExpression(expr.getExpr());
			if (m_resultValue != null)
				m_resultValue = m_resultValue.negative();
			break;
		case LOGICNEG :
			// TODO: boolean abstract domain... !!
		case OLD :
			// TODO: trace back? keep reference in abstract state?
		default:
			// TODO: support!
			AbstractInterpreter.s_logger.warn(String.format("Unsupported %s operator: %s", expr.getClass(), expr.getOperator()));
		}
	}

	protected void visit(StructConstructor expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(StructAccessExpression expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(StringLiteral expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(RealLiteral expr) {
		m_resultValue = AbstractInterpreter.s_domainFactory.makeRealValue(expr.getValue());
	}

	protected void visit(QuantifierExpression expr) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(IntegerLiteral expr) {
		m_resultValue = AbstractInterpreter.s_domainFactory.makeIntegerValue(expr.getValue());
	}

	protected void visit(IfThenElseExpression expr) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(IdentifierExpression expr) {
		m_resultValue = m_currentState.readValue(expr.getIdentifier());
	}

	protected void visit(FunctionApplication expr) {
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(BooleanLiteral expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(BitVectorAccessExpression expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(BitvecLiteral expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(BinaryExpression expr) {
		IAbstractValue left, right;
		left = evaluateExpression(expr.getLeft());
		right = evaluateExpression(expr.getRight());
		if ((left == null) || (right == null)) {
			AbstractInterpreter.s_logger.warn(String.format("Encountered null values in an %s", expr.getClass()));
			m_resultValue = null;
			return;
		}
		switch (expr.getOperator()) {
		case COMPLT :
			m_resultValue = left.compareIsLess(right);
			break;
		case COMPGT :
			m_resultValue = left.compareIsGreater(right);
			break;
		case COMPLEQ :
			m_resultValue = left.compareIsLessEqual(right);
			break;
		case COMPGEQ :
			m_resultValue = left.compareIsGreaterEqual(right);
			break;
		case COMPEQ :
			m_resultValue = left.compareIsEqual(right);
			break;
		case COMPNEQ :
			m_resultValue = left.compareIsNotEqual(right);
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
		case COMPPO :
		case BITVECCONCAT :
		default :
			// TODO: support!
			AbstractInterpreter.s_logger.warn(String.format("Unsupported %s operator: %s", expr.getClass(), expr.getOperator()));
		}
	}

	protected void visit(ArrayStoreExpression expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}

	protected void visit(ArrayAccessExpression expr) {
		// TODO: support!
		AbstractInterpreter.s_logger.warn(String.format("Unsupported expression type: %s", expr.getClass()));
	}
}
