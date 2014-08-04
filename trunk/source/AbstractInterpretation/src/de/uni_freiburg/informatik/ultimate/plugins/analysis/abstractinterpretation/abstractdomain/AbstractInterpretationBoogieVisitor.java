/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue.Bool;

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
	
	private final Logger m_logger;
	
	private final BoogieSymbolTable m_symbolTable;
	
	private final IAbstractDomainFactory<?> m_numberFactory;
	
	private final BoolDomainFactory m_boolFactory;
	
	/**
	 * The identifier for an LHS expression
	 * TODO: what about arrays and structs?
	 */
	private String m_lhsIdentifier;
	
	private IType m_lhsType;
	
	private Map<Expression, IAbstractValue<?>> m_interimResults = new HashMap<Expression, IAbstractValue<?>>();
	
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
	
	public AbstractInterpretationBoogieVisitor(Logger logger, BoogieSymbolTable symbolTable,
			IAbstractDomainFactory<?> numberFactory, BoolDomainFactory boolFactory) {
		m_logger = logger;
		m_symbolTable = symbolTable;
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
		
		m_interimResults.clear();
		
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

		m_interimResults.clear();
		
		return m_resultingState;
	}

	protected void visit(ReturnStatement statement) {
		// TODO: support! (pop stack?)
		m_logger.warn(String.format("Unsupported statement type: %s", statement.getClass()));
	}

	protected void visit(HavocStatement statement) {
		// TODO: arrays/structs
		LeftHandSide[] lhs = statement.getIdentifiers();
		for (int i = 0; i < lhs.length; i++) {
			m_lhsType = null;
			evaluateLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			if (m_lhsType != null) {
				if (m_lhsType instanceof PrimitiveType) {
					PrimitiveType pt = (PrimitiveType) m_lhsType;
					IAbstractValue<?> havocedValue = null;
					if (pt.getTypeCode() == PrimitiveType.BOOL) {
						havocedValue = m_boolFactory.makeTopValue();
					} else if ((pt.getTypeCode() == PrimitiveType.INT)
							|| (pt.getTypeCode() == PrimitiveType.REAL)) {
						havocedValue = m_numberFactory.makeTopValue();
					} else {
						m_logger.error(String.format("Unknown primitive type \"%s\" of left hand side \"%s\".", pt, lhs[i]));
					}
					if (havocedValue != null) {
						if (!m_resultingState.writeValue(m_lhsIdentifier, havocedValue)) {
							m_resultingState.declareIdentifier(m_lhsIdentifier, havocedValue);
						}
					}
				}
			} else {
				m_logger.error(String.format("Type of left hand side \"%s\" could not be determined.", lhs[i]));
			}
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
			// TODO: arrays/structs
			m_lhsType = null;
			evaluateLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			IAbstractValue<?> rhsValue = evaluateExpression(rhs[i]);
			boolean writeSuccessful = m_resultingState.writeValue(m_lhsIdentifier, rhsValue);
			if (!writeSuccessful) {
				if (m_lhsType != null) {
					if (m_lhsType instanceof PrimitiveType) {
						PrimitiveType pt = (PrimitiveType) m_lhsType;
						if (pt.getTypeCode() == PrimitiveType.BOOL) {
							m_resultingState.declareIdentifier(m_lhsIdentifier, m_boolFactory.makeTopValue());
						} else if ((pt.getTypeCode() == PrimitiveType.INT)
								|| (pt.getTypeCode() == PrimitiveType.REAL)) {
							m_resultingState.declareIdentifier(m_lhsIdentifier, m_numberFactory.makeTopValue());
						} else {
							m_logger.error(String.format("Unknown primitive type \"%s\" of left hand side \"%s\".", pt, lhs[i]));
						}
					}
				} else {
					m_logger.error(String.format("Type of left hand side \"%s\" could not be determined.", lhs[i]));
				}
			}
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
		
		// reconstruct variable values that pass through the formula, adjust resulting statement
		applyAssumption(statement.getFormula());
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
		m_lhsType = lhs.getType();
	}

	protected void visit(StructLHS lhs) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
		//evaluateLeftHandSide(lhs.getStruct());
		//m_lhsIdentifier = m_lhsIdentifier + "!" + lhs.getField();
		m_lhsType = lhs.getType();
	}

	protected void visit(ArrayLHS lhs) {
		// TODO: support!
		m_logger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
		m_lhsType = lhs.getType();
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
		
		m_interimResults.put(expr, m_resultValue);
		IAbstractValue<?> returnValue = m_resultValue;
		m_resultValue = backup; // restore result value
		return returnValue;
	}

	/**
	 * Evaluate the expression as if it was !(expr)
	 * @param expr
	 * @return
	 */
	protected IAbstractValue<?> evaluateNegatedExpression(Expression expr) {
		setNegate();
		return evaluateExpression(expr);
	}

	protected void visit(UnaryExpression expr) {
		switch (expr.getOperator()) {
		case ARITHNEGATIVE:
			m_resultValue = evaluateExpression(expr.getExpr());
			if (m_resultValue != null)
				m_resultValue = m_resultValue.negative();
			break;
		case LOGICNEG :
			m_resultValue = evaluateNegatedExpression(expr.getExpr());
			break;
		case OLD :
			// TODO: trace back? keep reference in abstract state?
		default:
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
		if (m_resultValue == null)
			m_resultValue = m_resultingState.readValue(expr.getIdentifier());
		if (m_resultValue == null) {
			// first time we encounter this identifier: look up in symbol table, impicit havoc to TOP
			String ident = expr.getIdentifier();
			IType t = m_symbolTable.getTypeForVariableSymbol(ident, StorageClass.LOCAL,
					m_resultingState.getCurrentScopeName()); // TODO: current scope; GLOBAL, in/put params...
			if (t != null) {
				if (t instanceof PrimitiveType) {
					PrimitiveType pt = (PrimitiveType) t;
					IAbstractValue<?> newValue = null;
					if (pt.getTypeCode() == PrimitiveType.BOOL) {
						newValue = m_boolFactory.makeTopValue();
					} else if ((pt.getTypeCode() == PrimitiveType.INT)
							|| (pt.getTypeCode() == PrimitiveType.REAL)) {
						newValue = m_numberFactory.makeTopValue();
					} else {
						m_logger.error(String.format("Unknown primitive type \"%s\" of identifier \"%s\".", pt, ident));
					}
					if (newValue != null) {
						m_resultValue = newValue;
						m_resultingState.declareIdentifier(ident, m_resultValue);
					}
				} else {
					m_logger.error(String.format("Unknown non-primitive type \"%s\" of identifier \"%s\".", t, ident));
				}
			} else {
				m_logger.error(String.format("Type of identifier \"%s\" could not be determined.", ident));
			}
		}
		if (m_resultValue == null) m_resultValue = m_numberFactory.makeBottomValue(); // prevent null value in an expression
	}

	protected void visit(BooleanLiteral expr) {
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
		IAbstractValue<?> left = null, right = null;
		switch (expr.getOperator()) {
		case COMPLT :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = neg ? left.compareIsGreaterEqual(right) : left.compareIsLess(right);
			break;
		case COMPGT :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = neg ? left.compareIsLessEqual(right) : left.compareIsGreater(right);
			break;
		case COMPLEQ :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = neg ? left.compareIsGreater(right) : left.compareIsLessEqual(right);
			break;
		case COMPGEQ :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = neg ? left.compareIsLess(right) : left.compareIsGreaterEqual(right);
			break;
		case COMPEQ :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = neg ? left.compareIsNotEqual(right) : left.compareIsEqual(right);
			break;
		case COMPNEQ :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = neg ? left.compareIsEqual(right) : left.compareIsNotEqual(right);
			break;
		case ARITHPLUS :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = left.add(right);
			break;
		case ARITHMINUS :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = left.subtract(right);
			break;
		case ARITHMUL :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = left.multiply(right);
			break;
		case ARITHDIV :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = left.divide(right);
			break;
		case ARITHMOD :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = left.modulo(right);
			break;
		case LOGICIFF :
		case LOGICIMPLIES :
		case LOGICAND :
		case LOGICOR :
			BoolValue leftBool = null, rightBool = null, result;
			switch (expr.getOperator()) {
			case LOGICIFF :
				if (neg) {
					// !(a <-> b) <=> (a || b) && (!a || !b)
					leftBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getRight()));
					BoolValue leftBool2 = leftBool.logicOr(rightBool);
					leftBool = m_boolFactory.makeFromAbstractValue(evaluateNegatedExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					BoolValue rightBool2 = leftBool.logicOr(rightBool);
					result = leftBool2.logicAnd(rightBool2);
				} else {
					leftBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getRight()));
					if (leftBool == null) return;
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicIff(rightBool);
				}
				break;
			case LOGICIMPLIES :
				leftBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getLeft()));
				if (leftBool == null) return;
				if (neg) {
					// !(a -> b) <=> a && !b
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					result = leftBool.logicImplies(rightBool);
				} else {
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicImplies(rightBool);
				}
				break;
			case LOGICAND :
				if (neg) {
					// !(a && b) <=> !a || !b
					leftBool = m_boolFactory.makeFromAbstractValue(evaluateNegatedExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					result = leftBool.logicOr(rightBool);
				} else {
					leftBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicAnd(rightBool);
				}
				break;
			case LOGICOR :
				if (neg) {
					// !(a || b) <=> !a && !b
					leftBool = m_boolFactory.makeFromAbstractValue(evaluateNegatedExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					result = leftBool.logicAnd(rightBool);
				} else {
					leftBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = m_boolFactory.makeFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicOr(rightBool);
				}
				break;
			default :
				result = m_boolFactory.makeBottomValue();
			}
			left = leftBool;
			right = rightBool;
			m_resultValue =  result;
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


	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * ASSUMPTIONS * * * TODO: General cases
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * Currently, only expressions "x ~ y" where x or y is a variable are covered. 
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
	
	/**
	 * Adjusts m_resultingState to narrow the possible values with information taken from
	 * an assume statement.
	 * @param assumeFormula The assume statement's formula expression
	 * @param assumeResult The AbstractValue representing the assume formula's result
	 */
	private void applyAssumption(Expression assumeFormula) {
		// only apply when the assumption can be true
		IAbstractValue<?> assumeResult = m_interimResults.get(assumeFormula);
		
		if (m_boolFactory.makeFromAbstractValue(assumeResult).getValue() == Bool.FALSE)
			return;
		
		if (assumeFormula instanceof BinaryExpression) {
			BinaryExpression binOp = (BinaryExpression) assumeFormula;
			m_logger.debug(String.format("ASSUME ## %s", assumeFormula.toString()));

			switch (binOp.getOperator()) {
			case LOGICAND :
				if (binOp.getLeft() instanceof BinaryExpression)
					applyAssumption(binOp.getLeft());
				if (binOp.getRight() instanceof BinaryExpression)
					applyAssumption(binOp.getRight());
			case COMPLT :
			case COMPGT :
			case COMPLEQ :
			case COMPGEQ :
			case COMPEQ :
			case COMPNEQ :
			case LOGICIFF :
			case LOGICIMPLIES :
			case LOGICOR :
				if (binOp.getLeft() instanceof IdentifierExpression) {
					IdentifierExpression ieLeft = (IdentifierExpression) binOp.getLeft();
					
					IAbstractValue<?> oldValue = m_resultingState.readValue(ieLeft.getIdentifier());
					if (oldValue != null) {
						IAbstractValue<?> newValue = oldValue.compareIsEqual(assumeResult);
						m_logger.debug(String.format("ASSUME ## [%s] == [%s] => [%s]", oldValue, assumeResult, newValue));
						if (newValue != null)
							m_resultingState.writeValue(ieLeft.getIdentifier(), newValue);
					}
				}

				if (binOp.getRight() instanceof IdentifierExpression) {
					IdentifierExpression ieRight = (IdentifierExpression) binOp.getRight();

					IAbstractValue<?> oldValue = m_currentState.readValue(ieRight.getIdentifier());
					if (oldValue != null) {
						IAbstractValue<?> newValue = oldValue.compareIsEqual(assumeResult);
						if (newValue != null)
							m_resultingState.writeValue(ieRight.getIdentifier(), newValue);
					}
				}
				break;
			default:
				break;
			}
			
		}
	}
}
