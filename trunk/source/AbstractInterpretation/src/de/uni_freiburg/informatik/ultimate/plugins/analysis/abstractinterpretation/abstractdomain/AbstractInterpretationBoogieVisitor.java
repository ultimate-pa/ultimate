/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState.ArrayData;

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

	private final IAbstractDomainFactory<?> m_intFactory;
	private final IAbstractDomainFactory<?> m_realFactory;
	private final IAbstractDomainFactory<?> m_boolFactory;
	private final IAbstractDomainFactory<?> m_bitVectorFactory;
	private final IAbstractDomainFactory<?> m_stringFactory;
	
	private final IAbstractValue<?> m_boolFalse;

	/**
	 * The identifier for an LHS expression
	 */
	private String m_lhsIdentifier;

	private String m_arrayIdentifier;
	
	private IType m_lhsType;
	
	private StorageClass m_lhsStorageClass;
	
	private Map<Expression, IAbstractValue<?>> m_interimResults = new HashMap<Expression, IAbstractValue<?>>();
	
	/**
	 * Flag for use with return statements, as both CALL and RETURN use CallStatement objects
	 */
	private boolean m_isReturnStatement = false;
	
	private boolean m_useOldValues = false;
	
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
			IAbstractDomainFactory<?> intFactory, IAbstractDomainFactory<?> realFactory,
			IAbstractDomainFactory<?> boolFactory, IAbstractDomainFactory<?> bitVectorFactory,
			IAbstractDomainFactory<?> stringFactory) {
		m_logger = logger;
		m_symbolTable = symbolTable;
		m_intFactory = intFactory;
		m_realFactory = realFactory;
		m_boolFactory = boolFactory;
		m_bitVectorFactory = bitVectorFactory;
		m_stringFactory = stringFactory;
		
		m_boolFalse = m_boolFactory.makeBoolValue(false); // used for assume evaluation
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
		
		if (statement instanceof HavocStatement) {
			visit((HavocStatement) statement);
		} else if (statement instanceof CallStatement) {
			CallStatement cs = (CallStatement) statement;
			if (m_isReturnStatement) visitReturn(cs); else visitCall(cs);
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

	/**
	 * Evaluates a return statement with regards to a current state and returns a resulting state 
	 * @param statement The return edges' corresponding call statement to evaluate
	 * @param currentState The current abstract program state
	 * @return The resulting abstract program state
	 */
	public AbstractState evaluateReturnStatement(CallStatement statement, AbstractState currentState) {
		m_isReturnStatement = true;
		AbstractState result = evaluateStatement(statement, currentState);
		m_isReturnStatement = false;
		return result;
	}

	protected void visitCall(CallStatement statement) {
		String methodName = statement.getMethodName();

		// add scope level for entered method
		m_resultingState.pushStackLayer(statement);
		
		m_logger.debug(String.format("CALL: %s", methodName));
		
		Expression[] arguments = statement.getArguments();
		
		// fetch method declaration to get input parameters
		List<Declaration> methodDecList = m_symbolTable.getFunctionOrProcedureDeclaration(methodName);
		if (methodDecList.size() >= 1) {
			Declaration methodDec = methodDecList.get(0);
			VarList[] parameters = null;
			if (methodDec instanceof FunctionDeclaration) {
				FunctionDeclaration functionDec = (FunctionDeclaration) methodDec;
				parameters = functionDec.getInParams();
			} else if (methodDec instanceof Procedure) {
				Procedure procedureDec = (Procedure) methodDec;
				parameters = procedureDec.getInParams();
			} else {
				m_logger.warn(String.format("Unknown method declaration kind \"%s\" encountered.", methodDec));
			}
			if (parameters != null) {
				// match input parameters to arguments
				if (parameters.length == arguments.length) {
					for (int i = 0; i < parameters.length; i++) {
						IAbstractValue<?> argValue = evaluateExpression(arguments[i]);
						String[] identifiers = parameters[i].getIdentifiers();
						if (identifiers.length != 1) {
							m_logger.warn(String.format("Invalid number method \"%s\" input parameter argument %d", methodName, i));
						} else {
							m_resultingState.declareIdentifier(identifiers[0], argValue, false);
						}
					}
				} else {
					m_logger.warn(String.format("Invalid number of arguments for method call of \"%s\"", methodName));
				}
			}
		}
	}

	protected void visitReturn(CallStatement statement) {
		CallStatement currentScopeCall = m_currentState.getCurrentScope().getCallStatement();
		
		if (currentScopeCall != statement) {
			// abort on not matching return
			m_resultingState = null;
			return;
		}

		String methodName = statement.getMethodName();

		// remove scope level of exited method
		m_resultingState.popStackLayer();
		
		m_logger.debug(String.format("RETURN: %s", methodName));

		LeftHandSide[] leftHandSides = statement.getLhs();
		
		// fetch method declaration to get input parameters
		List<Declaration> methodDecList = m_symbolTable.getFunctionOrProcedureDeclaration(methodName);
		if (methodDecList.size() >= 1) {
			Declaration methodDec = methodDecList.get(0);
			VarList[] parameters = null;
			if (methodDec instanceof FunctionDeclaration) {
				FunctionDeclaration functionDec = (FunctionDeclaration) methodDec;
				parameters = new VarList[]{functionDec.getOutParam()};
			} else if (methodDec instanceof Procedure) {
				Procedure procedureDec = (Procedure) methodDec;
				parameters = procedureDec.getOutParams();
			} else {
				m_logger.warn(String.format("Unknown method declaration kind \"%s\" encountered.", methodDec));
			}
			if (parameters != null) {
				// get value for each output parameter && write it to the destination variable
				if (parameters.length == leftHandSides.length) {
					for (int i = 0; i < parameters.length; i++) {
						String[] identifiers = parameters[i].getIdentifiers();
						if (identifiers.length != 1) {
							m_logger.warn(String.format("Invalid number of identifiers for method \"%s\" output parameter argument %d", methodName, i));
						} else {
							IAbstractValue<?> returnValue = m_currentState.readValue(identifiers[0], false);
							if (returnValue == null)
								returnValue = getTopValueForType(parameters[i].getType().getBoogieType());
							evaluateLeftHandSide(leftHandSides[i]);
							boolean writeSuccessful = m_resultingState.writeValue(m_lhsIdentifier, returnValue);
							if (!writeSuccessful)
								m_resultingState.declareIdentifier(m_lhsIdentifier, returnValue, m_lhsStorageClass == StorageClass.GLOBAL);
						}
					}
				} else {
					m_logger.warn(String.format("Invalid number of result parameters for method return of \"%s\"", methodName));
				}
			}
		}
	}

	protected void visit(HavocStatement statement) {
		LeftHandSide[] lhs = statement.getIdentifiers();
		for (int i = 0; i < lhs.length; i++) {
			m_lhsType = null;
			evaluateLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			if (m_lhsIdentifier != null)
				havocValue(m_lhsIdentifier, m_lhsType, m_lhsStorageClass);
		}
	}

	protected void visit(AssignmentStatement statement) {
		LeftHandSide[] lhs = statement.getLhs();
		Expression[] rhs = statement.getRhs();
		
		if (lhs.length != rhs.length) {
			m_logger.warn(String.format("%s lhs and rhs size mismatch!", statement.getClass()));
			return;
		}

		for (int i = 0; i < lhs.length; i++) {
			m_lhsType = null;
			evaluateLeftHandSide(lhs[i]); // get identifier to m_lhsIdentifier
			if (m_lhsIdentifier != null) {
				String identifier = m_lhsIdentifier;
				IAbstractValue<?> rhsValue = evaluateExpression(rhs[i]); // may change m_lhsIdentifier in an ArrayAccessExpression
				if (rhsValue != null) {
					m_logger.debug(String.format("Assignment: %s := %s", identifier, rhsValue));
					boolean writeSuccessful = m_resultingState.writeValue(identifier, rhsValue);
					if (!writeSuccessful)
						m_resultingState.declareIdentifier(identifier, rhsValue, m_lhsStorageClass == StorageClass.GLOBAL);
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
		
		if (assumptionValueIsFalse(formulaResult)) {
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
		} else if (lhs instanceof VariableLHS) {
			visit((VariableLHS) lhs);
		} else {
			throw new UnsupportedOperationException(String.format("Unsupported LeftHandSide type %s", lhs.getClass()));
		}
	}
	
	protected void visit(VariableLHS lhs) {
		m_lhsIdentifier = lhs.getIdentifier();
		m_lhsType = lhs.getType();
		m_lhsStorageClass = lhs.getDeclarationInformation().getStorageClass();
	}

	protected void visit(ArrayLHS lhs) {
		m_logger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
		m_lhsIdentifier = null;
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
		} else if (expr instanceof UnaryExpression) {
			visit((UnaryExpression) expr);
		} else {
			m_logger.error(String.format("Unsupported expression class ", expr.getClass()));
		}
		
		if (m_resultValue != null)
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
			boolean useOld_bak = m_useOldValues;
			m_useOldValues = true;
			m_resultValue = evaluateExpression(expr.getExpr());
			m_useOldValues = useOld_bak;
			break;
		default:
			m_logger.warn(String.format("Unsupported %s operator: %s", expr.getClass(), expr.getOperator()));
		}
	}

	protected void visit(StringLiteral expr) {
		m_resultValue = m_stringFactory.makeStringValue(expr.getValue());
	}

	protected void visit(RealLiteral expr) {
		m_resultValue = m_realFactory.makeRealValue(expr.getValue());
	}

	protected void visit(IntegerLiteral expr) {
		m_resultValue = m_intFactory.makeIntegerValue(expr.getValue());
	}

	protected void visit(IdentifierExpression expr) {
		boolean negate = doNegate();
		getValueOfIdentifier(expr.getIdentifier(), expr.getType(),
				expr.getDeclarationInformation().getStorageClass());
		if (negate)
			m_resultValue = m_resultValue.logicNot();
	}

	protected void visit(BooleanLiteral expr) {
		boolean val = expr.getValue();
		val = doNegate() ? !val : val;
		m_resultValue = m_boolFactory.makeBoolValue(val);
	}

	protected void visit(BitVectorAccessExpression expr) {
		IAbstractValue<?> bitVec = evaluateExpression(expr.getBitvec());
		if (bitVec == null)
			m_resultValue = null;
		
		m_resultValue = bitVec.bitVectorAccess(expr.getStart(), expr.getEnd());
	}

	protected void visit(BitvecLiteral expr) {
		m_resultValue = m_bitVectorFactory.makeBitVectorValue(expr.getValue());
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
			IAbstractValue<?> leftBool = null, rightBool = null, result;
			switch (expr.getOperator()) {
			case LOGICIFF :
				if (neg) {
					// !(a <-> b) <=> (a || b) && (!a || !b)
					leftBool = booleanFromAbstractValue(evaluateExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = booleanFromAbstractValue(evaluateExpression(expr.getRight()));
					IAbstractValue<?> leftBool2 = leftBool.logicOr(rightBool);
					leftBool = booleanFromAbstractValue(evaluateNegatedExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = booleanFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					IAbstractValue<?> rightBool2 = leftBool.logicOr(rightBool);
					result = leftBool2.logicAnd(rightBool2);
				} else {
					leftBool = booleanFromAbstractValue(evaluateExpression(expr.getRight()));
					if (leftBool == null) return;
					rightBool = booleanFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicIff(rightBool);
				}
				break;
			case LOGICIMPLIES :
				leftBool = booleanFromAbstractValue(evaluateExpression(expr.getLeft()));
				if (leftBool == null) return;
				if (neg) {
					// !(a -> b) <=> a && !b
					rightBool = booleanFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					result = leftBool.logicImplies(rightBool);
				} else {
					rightBool = booleanFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicImplies(rightBool);
				}
				break;
			case LOGICAND :
				if (neg) {
					// !(a && b) <=> !a || !b
					leftBool = booleanFromAbstractValue(evaluateNegatedExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = booleanFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					result = leftBool.logicOr(rightBool);
				} else {
					leftBool = booleanFromAbstractValue(evaluateExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = booleanFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicAnd(rightBool);
				}
				break;
			case LOGICOR :
				if (neg) {
					// !(a || b) <=> !a && !b
					leftBool = booleanFromAbstractValue(evaluateNegatedExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = booleanFromAbstractValue(evaluateNegatedExpression(expr.getRight()));
					result = leftBool.logicAnd(rightBool);
				} else {
					leftBool = booleanFromAbstractValue(evaluateExpression(expr.getLeft()));
					if (leftBool == null) return;
					rightBool = booleanFromAbstractValue(evaluateExpression(expr.getRight()));
					result = leftBool.logicOr(rightBool);
				}
				break;
			default :
				result = m_boolFactory.makeBottomValue();
			}
			left = leftBool;
			right = rightBool;
			m_resultValue = result;
			break;
		case BITVECCONCAT :
			left = evaluateExpression(expr.getLeft());
			if (left == null) return;
			right = evaluateExpression(expr.getRight());
			m_resultValue = left.bitVectorConcat(right);
			break;
		case COMPPO :
		default :
			m_logger.warn(String.format("Unsupported %s operator: %s", expr.getClass(), expr.getOperator()));
		}
		m_logger.debug(String.format("BinOp [%s] %s%s [%s] = [%s]", left, neg ? "NOT " : "", expr.getOperator(), right, m_resultValue));
	}

	protected void visit(ArrayStoreExpression expr) {
		m_resultValue = evaluateExpression(expr.getValue());
		boolean onlySingleIndices = evaluateArrayIdentifier(expr.getArray(), expr.getIndices());

		// adjust array's collective merged value
		ArrayData arrayData = getArrayData(m_arrayIdentifier);
		mergeArrayValue(arrayData, m_resultValue);
		
		if (onlySingleIndices) {
			// store value
			m_logger.debug(String.format("Array store: %s := %s", m_lhsIdentifier, m_resultValue));
			boolean writeSuccessful = m_resultingState.writeValue(m_lhsIdentifier, m_resultValue);
			if (!writeSuccessful)
				m_resultingState.declareIdentifier(m_lhsIdentifier, m_resultValue, m_lhsStorageClass == StorageClass.GLOBAL);
		} else {
			m_logger.debug(String.format("Array store with ambiguous indices: %s", m_lhsIdentifier));

			// Store that array has a value written to ambiguous indices
			arrayData.setIndicesUnclear();
		}
			
		// since we already stored the value, make sure the AssignmentStatement doesn't do it
		m_resultValue = null;
	}

	protected void visit(ArrayAccessExpression expr) {
		boolean onlySingleIndices = evaluateArrayIdentifier(expr.getArray(), expr.getIndices());
		
		ArrayData arrayData = getArrayData(m_arrayIdentifier);
		
		if (onlySingleIndices) {
			boolean hasValue = getValueOfIdentifier(m_lhsIdentifier, m_lhsType, m_lhsStorageClass);
			if (arrayData.getIndicesUnclear() && hasValue) {
				m_resultValue = arrayData.getValue();
			} else {
				// merge into collective array data value in case of havoc on m_lhsIdentifier
				mergeArrayValue(arrayData, m_resultValue);
			}
			m_logger.debug(String.format("Array Read: %s -> %s", m_lhsIdentifier, m_resultValue));
		} else {
			m_logger.debug(String.format("Array read with ambiguous indices: %s", m_lhsIdentifier));
			
			// return top value as we don't know which array index to access
			m_resultValue = getTopValueForType(m_lhsType);
		}
	}

	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * MISC
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
	
	/**
	 * @param array
	 * @param indices
	 * @return True iff the array is only accesses by a single concrete value per index
	 */
	private boolean evaluateArrayIdentifier(Expression array, Expression[] indices) {
		// assume array is a VariableLHS
		String arrayIdentifier = null;
		String variableIdentifier = null;
		IType type = null;
		StorageClass storageClass = null;
		if (array instanceof IdentifierExpression) {
			IdentifierExpression arrayIdent = (IdentifierExpression) array;
			variableIdentifier = arrayIdentifier = arrayIdent.getIdentifier();
			type = arrayIdent.getType();
			if (type instanceof ArrayType)
				type = ((ArrayType) type).getValueType();
			storageClass = arrayIdent.getDeclarationInformation().getStorageClass();
		} else if (array instanceof ArrayAccessExpression) {
			ArrayAccessExpression arrayAccess = (ArrayAccessExpression) array;
			evaluateArrayIdentifier(arrayAccess.getArray(), arrayAccess.getIndices());
			variableIdentifier = m_lhsIdentifier;
			storageClass = m_lhsStorageClass;
			type = m_lhsType;
		} else {
			m_logger.error(String.format("Unsupported array identifier found: %s", array));
			m_lhsIdentifier = null;
			m_lhsType = null;
			m_resultValue = null;
			return false;
		}
		
		IAbstractValue<?>[] indexValues = new IAbstractValue<?>[indices.length];
		boolean onlySingleIndices = true;
		for (int i = 0; i < indices.length; i++) {
			indexValues[i] = evaluateExpression(indices[i]);
			variableIdentifier += String.format("[%s]", indexValues[i]);
			onlySingleIndices = (indexValues[i] != null) && indexValues[i].representsSingleConcreteValue();
			if (!onlySingleIndices) break;
		}
		m_lhsIdentifier = variableIdentifier;
		m_arrayIdentifier = arrayIdentifier;
		m_lhsType = type;
		m_lhsStorageClass = storageClass;
		
		return onlySingleIndices;
	}
	
	private ArrayData getArrayData(String arrayIdentifier) {
		Map<String, ArrayData> arrayDataMap =
				(m_lhsStorageClass == StorageClass.GLOBAL ?
						m_resultingState.getGlobalScope() :
						m_resultingState.getCurrentScope()).getArrays();
		ArrayData arrayData = arrayDataMap.get(arrayIdentifier);
		if (arrayData == null) {
			arrayData = m_resultingState.new ArrayData(arrayIdentifier);
			arrayDataMap.put(arrayIdentifier, arrayData);
		}
		return arrayData;
	}
	
	private void mergeArrayValue(ArrayData arrayData, IAbstractValue<?> value) {
		if (value == null)
			return;
		
		IAbstractValue<?> oldValue = arrayData.getValue();
		if (oldValue == null) {
			arrayData.setValue(value);
		} else if (!oldValue.isSuper(value)) {
			IMergeOperator<?> mop = null;
			if (m_boolFactory.valueBelongsToDomainSystem(oldValue)) {
				mop = m_boolFactory.getMergeOperator();
			} else if (m_bitVectorFactory.valueBelongsToDomainSystem(oldValue)) {
				mop = m_bitVectorFactory.getMergeOperator();
			} else if (m_stringFactory.valueBelongsToDomainSystem(oldValue)) {
				mop = m_stringFactory.getMergeOperator();
			} else if (m_intFactory.valueBelongsToDomainSystem(oldValue)) {
				mop = m_intFactory.getMergeOperator();
			} else if (m_realFactory.valueBelongsToDomainSystem(oldValue)) {
				mop = m_realFactory.getMergeOperator();
			}
			if (mop != null) {
				IAbstractValue<?> newValue = mop.apply(oldValue, value);
				arrayData.setValue(newValue);
			} else {
				m_logger.warn(String.format("Can't create merge operator for value %s", oldValue));
			}
		}
	}

	/**
	 * Stores the value of the given identifier in m_resultValue, with havoc if necessary
	 * @param identifier
	 * @param type Used if havoc is required
	 * @param storageClass Used if havoc is required
	 * @return True iff a value existed already, false if a havoc was performed
	 */
	private boolean getValueOfIdentifier(String identifier, IType type, StorageClass storageClass) {
		m_resultValue = m_currentState.readValue(identifier, m_useOldValues);
		if ((m_resultValue == null) && !m_useOldValues)
			m_resultValue = m_resultingState.readValue(identifier, m_useOldValues);
		if (m_resultValue == null) {
			// first time we encounter this identifier: look up in symbol table, implicit havoc to TOP
			m_resultValue = havocValue(identifier, type, storageClass);
			return false;
		}
		return true;
	}
	
	private IAbstractValue<?> getTopValueForType(IType type) {
		if (type == null) return null;
		if (type instanceof PrimitiveType) {
			PrimitiveType pt = (PrimitiveType) type;
			IAbstractValue<?> topValue = null;
			if (pt.getTypeCode() == PrimitiveType.BOOL) {
				topValue = m_boolFactory.makeTopValue();
			} else if (pt.getTypeCode() == PrimitiveType.INT) {
				topValue = m_intFactory.makeTopValue();
			} else if (pt.getTypeCode() == PrimitiveType.REAL) {
				topValue = m_realFactory.makeTopValue();
			} else {
				m_logger.error(String.format("Unsupported primitive type \"%s\"", pt));
			}
			return topValue;
		} else {
			m_logger.error(String.format("Unsupported non-primitive type \"%s\" of %s", type, type.getClass()));
			return null;
		}
	}
	
	private IAbstractValue<?> havocValue(String identifier, IType type, StorageClass storageClass) {
		// is an array?
		if (type instanceof ArrayType) {
			ArrayData arrayData = getArrayData(identifier);
			arrayData.setIndicesUnclear();
			arrayData.setValue(getTopValueForType(((ArrayType) type).getValueType()));
			// no need to havoc any individual values, since now only the global one will be accessed
		}
		
		// not an array
		if (type != null) {
			IAbstractValue<?> newValue = getTopValueForType(type);
			if (newValue != null) {
				IAbstractValue<?> result = newValue;
				boolean isGlobal = storageClass == StorageClass.GLOBAL;
				if (!(m_useOldValues && isGlobal)) {
					boolean writeSuccessful = m_resultingState.writeValue(identifier, result);
					if (!writeSuccessful)
						m_resultingState.declareIdentifier(identifier, result, isGlobal);
				}
				m_logger.debug(String.format("Havoc: %s\"%s\" := \"%s\".", m_useOldValues ? "old " : "", identifier, result));
				return result;
			}
		} else {
			m_logger.error(String.format("Unknown type of identifier \"%s\"", identifier));
		}
		return null;
	}
	
	/**
	 * @param value An abstract value to get a boolean value for
	 * @return A value in the boolean domain representing the given value:
	 * <br> If it already is a value in the boolean domain, a copy is returned.
	 * <br> Else, a boolean value of FALSE is returned iff the given value is bottom.
	 */
	public IAbstractValue<?> booleanFromAbstractValue(IAbstractValue<?> value) {
		if (m_boolFactory.valueBelongsToDomainSystem(value))
			return value.copy();
		
		return m_boolFactory.makeBoolValue(!value.isBottom());
	}

	/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * ASSUMPTIONS * * * TODO: General cases
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
	 * Currently, only expressions "x ~ y" where x or y is a variable are covered. 
	 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
	
	private boolean assumptionValueIsFalse(IAbstractValue<?> assumptionValue) {
		if (assumptionValue.isBottom())
			return true;
		
		if (m_boolFactory.valueBelongsToDomainSystem(assumptionValue)
				&& m_boolFalse.isEqual(assumptionValue))
			return true;
		
		return false;
	}
	
	/**
	 * Adjusts m_resultingState to narrow the possible values with information taken from
	 * an assume statement.
	 * @param assumeFormula The assume statement's formula expression
	 * @param assumeResult The AbstractValue representing the assume formula's result
	 */
	private boolean applyAssumption(Expression assumeFormula) {
		return applyAssumption(assumeFormula, false);
	}
	
	private boolean applyAssumption(Expression assumeFormula, boolean negate) {
		// only apply when the assumption can be true
		IAbstractValue<?> assumeResult = m_interimResults.get(assumeFormula);
		
		if (assumptionValueIsFalse(assumeResult))
			return false;
		
		boolean didNarrow = false;
		
		if (assumeFormula instanceof BinaryExpression) {
			BinaryExpression binOp = (BinaryExpression) assumeFormula;

			switch (binOp.getOperator()) {
			case LOGICAND :
				if (binOp.getLeft() instanceof BinaryExpression)
					didNarrow = applyAssumption(binOp.getLeft()) || didNarrow;
				if (binOp.getRight() instanceof BinaryExpression)
					didNarrow = applyAssumption(binOp.getRight()) || didNarrow;
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

					didNarrow = applyAssumptionResult(ieLeft.getIdentifier(), assumeResult) || didNarrow;
				}

				/*
				 *  Not all comparision operators can simply be "mirrored" (e.g. [5,5] < [10,10] = [5,5], [10,10] > [5,5] = [10,10],
				 *  so for some of them, we need to calculate the missing intermediate result
				 */
				if (binOp.getRight() instanceof IdentifierExpression) {
					IdentifierExpression ieRight = (IdentifierExpression) binOp.getRight();

					IAbstractValue<?> leftValue = m_interimResults.get(binOp.getLeft());
					IAbstractValue<?> rightValue = m_interimResults.get(ieRight);

					IAbstractValue<?> rightHandAssumeResult;
					switch (binOp.getOperator()) {
					case COMPLT :
						rightHandAssumeResult = negate ?
								rightValue.compareIsLess(leftValue) :
									rightValue.compareIsGreaterEqual(leftValue);
						break;
					case COMPGT :
						rightHandAssumeResult = negate ?
								rightValue.compareIsGreater(leftValue) :
									rightValue.compareIsLessEqual(leftValue);
						break;
					case COMPLEQ :
						rightHandAssumeResult = negate ?
								rightValue.compareIsLessEqual(leftValue) :
									rightValue.compareIsGreater(leftValue);
						break;
					case COMPGEQ :
						rightHandAssumeResult = negate ?
								rightValue.compareIsGreaterEqual(leftValue) :
									rightValue.compareIsLess(leftValue);
						break;
					case COMPEQ :
					case COMPNEQ :
						rightHandAssumeResult = assumeResult;
					case LOGICAND :
					case LOGICIFF :
					case LOGICIMPLIES :
					case LOGICOR :
					default:
						// case not covered
						rightHandAssumeResult = null;
					}
					if (rightHandAssumeResult != null)
						didNarrow = applyAssumptionResult(ieRight.getIdentifier(), rightHandAssumeResult) || didNarrow;
				}
				break;
			default:
				break;
			}
			
		} else if (assumeFormula instanceof UnaryExpression) {
			UnaryExpression unaryFormula = (UnaryExpression) assumeFormula;
			if (unaryFormula.getOperator() == UnaryExpression.Operator.LOGICNEG)
				didNarrow = applyAssumption(unaryFormula.getExpr(), true) || didNarrow;
		} else if (assumeFormula instanceof BooleanLiteral) {
			didNarrow = true; // "assume true;" -> nothing to narrow
		}
		if (!didNarrow)
			m_logger.warn(String.format("Could not narrow values at assume statement \"%s\"", assumeFormula));
		return didNarrow;
	}
	
	private boolean applyAssumptionResult(String identifier, IAbstractValue<?> assumeResult) {
		IAbstractValue<?> oldValue = m_resultingState.readValue(identifier, false);
		if (oldValue != null) {
			IAbstractValue<?> newValue = oldValue.compareIsEqual(assumeResult);
			m_logger.debug(String.format("ASSUME for \"%s\": old[%s], assume[%s] => new[%s]",
					identifier, oldValue, assumeResult, newValue));
			if (newValue != null) {
				m_resultingState.writeValue(identifier, newValue);
				return true;
			}
		}
		return false;
	}
}
