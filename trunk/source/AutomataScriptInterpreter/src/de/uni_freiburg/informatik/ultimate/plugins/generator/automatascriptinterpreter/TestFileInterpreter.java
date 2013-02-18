package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.lang.reflect.Method;
import java.util.*;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.*;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.*;


enum Flow {
	NORMAL, BREAK, CONTINUE, RETURN;
}
public class TestFileInterpreter {
	class TestCase {
		private Boolean m_assertionState;
		private ILocation m_location;
		
		private TestCase(boolean state, ILocation loc) {
			m_assertionState = state;
			m_location = loc;
		}
		
		private String getAssertionSummary() {
			return "Test at line " + m_location.getStartLine() + " is " + m_assertionState;
		}
	}
	
	private Map<String, Object> m_variables;
	private Flow m_flow;
	private AutomataDefinitionInterpreter m_automInterpreter;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private List<TestCase> m_testCases;
	
	public TestFileInterpreter() {
		m_variables = new HashMap<String, Object>();
		m_flow = Flow.NORMAL;
		m_automInterpreter = new AutomataDefinitionInterpreter();
		m_testCases = new ArrayList<TestCase>();
	}
	
	public Object interpretTestFile(AtsASTNode node) throws Exception {
		List<AtsASTNode> children = node.getOutgoingNodes();
		if (children.size() != 2) {
			s_Logger.warn("AtsASTNode should have 2 children!");
			s_Logger.warn("It has: " + children.size() + " children.");
		}
		
		if (children.get(1) instanceof AutomataDefinitions) {
			m_automInterpreter.interpret((AutomataDefinitions) children.get(1));
		}
		
		m_variables.putAll(m_automInterpreter.getAutomata());
		Object result = interpret(children.get(0));
		s_Logger.info(getTestCasesSummary());
		return result;

	}
	
	private <T> Object interpret(AssignmentExpression as) throws Exception {
		List<AtsASTNode> children = as.getOutgoingNodes();
		if (children.size() != 2) {
			String message = "AssignmentExpression: It should have 2 children.\n";
			message = message.concat("On the left-hand side there  must be a VariableExpression, ");
			message = message.concat("On the right-hand side there can be an arbitrary expression.");
			throw new Exception(message);
		}
		VariableExpression var = (VariableExpression) children.get(0);
		if (!m_variables.containsKey(var.getIdentifier())) {
			String message = "AssignmentExpression: Variable " + var.getIdentifier() + " was not declared.";
			throw new Exception(message);
		}
		Object oldValue = m_variables.get(var.getIdentifier());
		// Check for correct types
		if (!var.isTypeCorrect(children.get(1).getReturnType())) {
			String message = "AssignmentExpression: Type error";
			message = message.concat(children.get(1).getReturnType() + " is not assignable to " + var.getReturnType());
			throw new IllegalArgumentException(message);
		}
		Object newValue = interpret(children.get(1));
		switch(as.getOperator()) {
		case ASSIGN: m_variables.put(var.getIdentifier(), newValue); break;
		case PLUSASSIGN: {
			Integer assignValue = ((Integer)oldValue) + ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		case MINUSASSIGN: {
			Integer assignValue = ((Integer)oldValue) - ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		case MULTASSIGN: {
			Integer assignValue = ((Integer)oldValue) * ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		case DIVASSIGN: {
			Integer assignValue = ((Integer)oldValue) / ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		default: {
			throw new UnsupportedOperationException("AssignmentExpression: This type of operator is not supported: " + as.getOperator());
		}
			
		}
		
		return oldValue;
	}
		
	private <T> Object interpret(AtsASTNode node) throws Exception {
		Object result = null;
		if (node instanceof AssignmentExpression) {
			result = interpret((AssignmentExpression) node);
		} else if (node instanceof BinaryExpression) {
			result = interpret((BinaryExpression) node);
		} else if (node instanceof BreakStatement) {
			result = interpret((BreakStatement) node);
		} else if (node instanceof ConditionalBooleanExpression) {
			result = interpret((ConditionalBooleanExpression) node);
		} else if (node instanceof ConstantExpression) {
			result = interpret((ConstantExpression) node);
		} else if (node instanceof ContinueStatement) {
			result = interpret((ContinueStatement) node);
		} else if (node instanceof ForStatement) {
			result = interpret((ForStatement) node);
		} else if (node instanceof IfElseStatement) {
			result = interpret((IfElseStatement) node);
		} else if (node instanceof IfStatement) {
			result = interpret((IfStatement) node);
		} else if (node instanceof Nestedword) {
			result = interpret((Nestedword) node);
		} else if (node instanceof NestedLassoword) {
			result = interpret((NestedLassoword) node);
		} else if (node instanceof OperationInvocationExpression) {
			result = interpret((OperationInvocationExpression) node);
		} else if (node instanceof RelationalExpression) {
			result = interpret((RelationalExpression) node);
		} else if (node instanceof ReturnStatement) {
			result = interpret((ReturnStatement) node);
		} else if (node instanceof ReturnStatement) {
			result = interpret((StatementList) node);
		} else if (node instanceof StatementList) {
			result = interpret((StatementList) node);
		} else if (node instanceof UnaryExpression) {
			result = interpret((UnaryExpression) node);
		} else if (node instanceof VariableDeclaration) {
			result = interpret((VariableDeclaration) node);
		} else if (node instanceof VariableExpression) {
			result = interpret((VariableExpression) node);
		} else if (node instanceof WhileStatement) {
			result = interpret((WhileStatement) node);
		}
		
		return result;
	}

	private <T> Integer interpret(BinaryExpression be) throws Exception {
		List<AtsASTNode> children = be.getOutgoingNodes();
		if (children.size() != 2) {
			throw new Exception("BinaryExpression should always have 2 children!\nNum of children: " + children.size());
		}
		// Check for correct types
		if (!children.get(0).isTypeCorrect(be.getReturnType())) {
			String message = "BinaryExpression: 1st child\n";
			message = message.concat("Expected: " + be.getReturnType() + "\tGot: " + children.get(0).getReturnType());
			throw new Exception(message);
		} else if (!children.get(1).isTypeCorrect(be.getReturnType())) {
			String message = "BinaryExpression: 2nd child\n";
			message = message.concat("Expected: " + be.getReturnType() + "\tGot: " + children.get(1).getReturnType());
			throw new Exception(message);
		}
		
		Integer v1 = (Integer) interpret(children.get(0));
		Integer v2 = (Integer) interpret(children.get(1));
		
		switch(be.getOperator()) {
		case PLUS: return v1 + v2;
		case MINUS: return v1 - v2;
		case MULTIPLICATION: return v1 * v2;
		case DIVISION: return v1 / v2;
		default: throw new UnsupportedOperationException("BinaryExpression: This type of operator is not supported: " + be.getOperator());
		}
	}
	
	private <T> Object interpret(BreakStatement bst) throws Exception {
		List<AtsASTNode> children = bst.getOutgoingNodes();
		if (children.size() != 0) {
			String message = "BreakStatement: Should not have any children.\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		
		// Change the flow
		m_flow = Flow.BREAK;
		return null;
	}
	
	private <T> Boolean interpret(ConditionalBooleanExpression cbe) throws Exception{
		List<AtsASTNode> children = cbe.getOutgoingNodes();
		if ((cbe.getOperator() == ConditionalBooleanOperator.NOT) && (children.size() != 1)) {
			throw new Exception("ConditionalBooleanExpression: NOT operator should have 1 operand!\nNum of operands: " + children.size());
		} else if ((cbe.getOperator() == ConditionalBooleanOperator.AND) && (children.size() != 2)) {
			throw new Exception("ConditionalBooleanExpression: AND operator should have 2 operands!\nNum of operands: " + children.size());
		} else if ((cbe.getOperator() == ConditionalBooleanOperator.OR) && (children.size() != 2)) {
			throw new Exception("ConditionalBooleanExpression: OR operator should have 2 operands!\nNum of operands: " + children.size());
		}
		// Check for correct types
		if (!children.get(0).isTypeCorrect(cbe.getReturnType())) {
			String message = "ConditionalBooleanExpression: 1st child\n";
			message = message.concat("Expected: " + cbe.getReturnType() + "\tGot: " + children.get(0).getReturnType());
			throw new IllegalArgumentException(message);
		}
		
		if ((children.size() == 2) && (!children.get(1).isTypeCorrect(cbe.getReturnType()))) {
			String message = "ConditionalBooleanExpression: 2nd child\n";
			message = message.concat("Expected: " + cbe.getReturnType() + "\tGot: " + children.get(1).getReturnType());
			throw new IllegalArgumentException(message);
		}
		
		switch (cbe.getOperator()) {
		case NOT: return !((Boolean) interpret(children.get(0)));
		case AND: {
			Boolean v1 = (Boolean) interpret(children.get(0));
			if (!v1) {return false;} // Short-circuit and
			Boolean v2 = (Boolean) interpret(children.get(1));
			return v2;
		}
		case OR: {
			Boolean v1 = (Boolean) interpret(children.get(0));
			if (v1) {return true;} // Short-circuit or
			Boolean v2 = (Boolean) interpret(children.get(1));
			return v2;
		} 
		default: {
	    	throw new UnsupportedOperationException("ConditionalBooleanExpression: This type of operator is not supported: " + cbe.getOperator());  
	      }
		}
	}

	private <T> Object interpret(ConstantExpression ce) {
		return ce.getValue();
	}
	
	private <T> Object interpret(ContinueStatement cst) throws Exception {
		List<AtsASTNode> children = cst.getOutgoingNodes();
		if (children.size() != 0) {
			String message = "ContinueStatement: Should not have any children.\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		// Change the flow
		m_flow  =  Flow.CONTINUE;
		return null;
	}
	
	private <T> Object interpret(ForStatement fs) throws Exception {
		List<AtsASTNode> children = fs.getOutgoingNodes();
		if (children.size() != 4) {
			String message = "ForStatement should have 4 children (condition, initStmt, updateStmt, stmtList)\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		Boolean loopCondition = false;
		if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
			String message = "ForStatement: 1st child is not a Boolean expression\n";
			message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
			throw new Exception(message);
		}
		// If the loopcondition is missing, we just execute the loop forever
		if (children.get(0) == null) {
			loopCondition = true;
		}
		// execute the initialization statement, if one is existing
		if (children.get(1) != null) {
			interpret(children.get(1));
		}
		if (loopCondition) {
			for (;;) {
				List<AtsASTNode> statementList =  children.get(3).getOutgoingNodes();
			secondLoop:
				for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (m_flow != Flow.NORMAL) {
						switch (m_flow) {
						case BREAK:
						case RETURN: {
							m_flow = Flow.NORMAL;
							return null;
						}
						case CONTINUE: {
							m_flow = Flow.NORMAL;
							break secondLoop;
						}
						}
					}
				}
				// execute the updatestatement
				if (children.get(2) != null) {
					interpret(children.get(2));
				}
			}
		} else {
			for (;(Boolean)interpret(children.get(0));) {
				List<AtsASTNode> statementList =  children.get(3).getOutgoingNodes();
			secondLoop:
				for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (m_flow != Flow.NORMAL) {
						switch (m_flow) {
						case BREAK:
						case RETURN: {
							m_flow = Flow.NORMAL;
							return null;
						}
						case CONTINUE: {
							m_flow = Flow.NORMAL;
							break secondLoop;
						}
						}
					}
				}
				// execute the updatestatement
				if (children.get(2) != null) {
					interpret(children.get(2));
				}
			}
		}
		return null;
	}
	
	private <T> Object interpret(IfElseStatement is) throws Exception {
		List<AtsASTNode> children = is.getOutgoingNodes();
		if (children.size() != 3) {
			String message = "IfElseStatement should have 3 children (Condition, Thenstatements, Elsestatements)";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		if (children.get(0).getReturnType() != Boolean.class) {
			String message = "IfElseStatement: 1st child is not a Boolean expression\n";
			message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
			throw new Exception(message);
		}
		if ((Boolean) interpret(children.get(0))) {
			interpret(children.get(1));
		} else {
			interpret(children.get(2));
		}
		return null;
	}
	
	private <T> Object interpret(IfStatement is) throws Exception {
		List<AtsASTNode> children = is.getOutgoingNodes();
		if (children.size() != 2) {
			String message = "IfStatement should have 2 children (condition, thenStatements)\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		if (children.get(0).getReturnType() != Boolean.class) {
			String message = "IfStatement: 1st child is not a Boolean expression\n";
			message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
			throw new Exception(message);
		}
		if ((Boolean) interpret(children.get(0))) {
			for (int i = 1; i < children.size(); i++) {
				interpret(children.get(i));
			}
		}
		return null;
	}
	
	private <T> Object interpret(Nestedword nw) throws Exception {
		return new NestedWord<String>(nw.getWordSymbols(), nw.getNestingRelation());
	}
	
	private <T> Object interpret(NestedLassoword nw) throws Exception {
		return null;
	}
	
	private <T> Object interpret(OperationInvocationExpression oe) throws Exception {
		List<AtsASTNode> children = oe.getOutgoingNodes();
		if (children.size() != 1) {
			String message = "OperationExpression should have only 1 child (ArgumentList)";
			message = message.concat("Num of children: " + children.size());
			throw new IllegalArgumentException(message);
		}
		
		ArrayList<Object> arguments = null;
		List<AtsASTNode> argsToInterpret = null;
		if (children.get(0) != null) {
			argsToInterpret = children.get(0).getOutgoingNodes();
			arguments = new ArrayList<Object>(argsToInterpret.size());
			// Interpret the arguments of this operation
			for (int i = 0; i < argsToInterpret.size(); i++) {
				arguments.add(interpret(argsToInterpret.get(i)));
			}
		}
		
		// Indicates whether this operation is an automaton operation,
		// e.g. accepts, notaccepts, complement, ...
		boolean isAutomatonOperation = false;
		Object automaton = null;
		Method methodObject = null;
		for (Object arg : argsToInterpret) {
			if (arg instanceof VariableExpression) {
				if (m_variables.containsKey(((VariableExpression)arg).getIdentifier())) {
					methodObject = hasOperation(m_variables.get(((VariableExpression) arg).getIdentifier()) , oe.getOperationName()); 
					if (methodObject != null) {
						isAutomatonOperation = true;
						automaton = m_variables.get(((VariableExpression) arg).getIdentifier());
						break;
					}
				}
			}
		}
		
		Object result = null;
		if (isAutomatonOperation) {
//			if (arguments.remove(automaton)) {
//				result = methodObject.invoke(automaton, arguments.toArray());
//				if ((result instanceof Boolean) || (result.getClass().isAssignableFrom(boolean.class))) {
//					m_testCases.add(new TestCase((Boolean)result, oe.getLocation()));
//				}
//			}
			IOperation op = getAutomataOperation(oe.getOperationName(), arguments);
			result = op.getResult();
			if ((result instanceof Boolean) || (result.getClass().isAssignableFrom(boolean.class))) {
				m_testCases.add(new TestCase((Boolean)result, oe.getLocation()));
			}
			return result;
		} else {
//			if (oe.getOperationName().equals("assert")) {
//				if ()
//				assert()
//			}
		}
		
		return null;
		
	}
	
	private <T> Boolean interpret(RelationalExpression re) throws Exception{
		List<AtsASTNode> children = re.getOutgoingNodes();
		if (children.size() != 2) {
			throw new Exception("RelationalExpression should always have 2 children!\nNum of children: " + children.size());
		}
		// Check for correct types
		if (!children.get(0).isTypeCorrect(re.getExpectingType())) {
			String message = "RelationalExpression: 1st child\n";
			message = message.concat("Expected: " + re.getExpectingType() + "\tGot: " + children.get(0).getReturnType());
			throw new Exception(message);
		} else if (!children.get(1).isTypeCorrect(re.getExpectingType())) {
			String message = "RelationalExpression: 2nd child\n";
			message = message.concat("Expected: " + re.getExpectingType() + "\tGot: " + children.get(1).getReturnType());
			throw new Exception(message);
		}
		if (re.getExpectingType() == Integer.class) {
			Integer v1 = (Integer) interpret(children.get(0));
			Integer v2 = (Integer) interpret(children.get(1));
			switch (re.getOperator()) {
			case GREATERTHAN: return v1 > v2;
			case LESSTHAN: return v1 < v2;
			case GREATER_EQ_THAN: return v1 >= v2;
			case LESS_EQ_THAN: return v1 <= v2;
			case EQ: return v1 == v2;
			case NOT_EQ: return v1 != v2;
			default: throw new UnsupportedOperationException("RelationalExpression: This type of operator is not supported: " + re.getOperator());
			}
		}
		return null;
	}
	
	private <T> Object interpret(ReturnStatement rst) throws Exception {
		List<AtsASTNode> children = rst.getOutgoingNodes();
		if ((children.size() != 0) && (children.size() != 1)) {
			String message = "ReturnStatement: Too many children\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		// Change the flow
		m_flow = Flow.RETURN;
		if (children.size() == 0) {
			return null;
		} else {
			return interpret(children.get(0));
		}
	}
	
	private <T> Object interpret(StatementList stmtList) throws Exception {
		for (AtsASTNode stmt : stmtList.getOutgoingNodes()) {
			interpret(stmt);
		}
		return null;
	}
	
    private <T> Integer interpret(UnaryExpression ue) throws Exception {
		  List<AtsASTNode> children = ue.getOutgoingNodes();
		  if (children.size() != 1) {
			  throw new Exception("UnaryExpression should always have 1 child!\nNum of children: " + children.size());
		  }
		  if (!(children.get(0) instanceof VariableExpression)) {
			  throw new Exception("Unary operators are applicable only on variables!\nYou want to apply it on " + children.get(0).getClass().getSimpleName());
		  }
		  // Check for correct types
		  if (!children.get(0).isTypeCorrect(ue.getReturnType())) {
				String message = "UnaryExpression: 1st child\n";
				message = message.concat("Expected: " + ue.getReturnType() + "\tGot: " + children.get(0).getReturnType());
				throw new Exception(message);
			}
		  VariableExpression var = (VariableExpression) children.get(0);
		  Integer oldVal = (Integer)interpret(var);
	      
	      switch(ue.getOperator()) {
	      case EXPR_PLUSPLUS: {
	    	  m_variables.put(var.getIdentifier(), oldVal + 1);
	    	  return oldVal;
	      }
	      case EXPR_MINUSMINUS: {
	    	  m_variables.put(var.getIdentifier(), oldVal - 1);
	    	  return oldVal;
	      }
	      case PLUSPLUS_EXPR: {
	    	  m_variables.put(var.getIdentifier(), oldVal + 1);
	    	  return oldVal + 1;
	      }
	      case MINUSMINUS_EXPR: {
	    	  m_variables.put(var.getIdentifier(), oldVal - 1);
	    	  return oldVal - 1;
	      }
	      default: {
	    	throw new UnsupportedOperationException("UnaryExpression: This type of operator is not supported: " + ue.getOperator());  
	      }
	      }
		}
	
    private <T> Object interpret(VariableDeclaration vd) throws Exception {
    	List<AtsASTNode> children = vd.getOutgoingNodes();
    	if ((children.size() != 0) && (children.size() != 1)) {
    		String message = "VariableDeclaration: should have 0 or 1 child. (the value to assign)";
			throw new Exception(message);
    	}
    	Object value = null;
    	if (children.size() == 1) {
    		value = interpret(children.get(0));
    	}
    	
    	for (String id : vd.getIdentifiers()) {
    		m_variables.put(id, value);
    	}
    	return null;
    }
    
	private <T> Object interpret(VariableExpression ve) throws Exception {
		if (!m_variables.containsKey(ve.getIdentifier())) {
			String message = "VariableExpression: Variable " + ve.getIdentifier() + " was not declared.";
			throw new Exception(message);
		}
		
		return m_variables.get(ve.getIdentifier());
	}
	
	private <T> Object interpret(WhileStatement ws) throws Exception {
		List<AtsASTNode> children = ws.getOutgoingNodes();
		if (children.size() != 2) {
			String message = "WhileStatement should have 2 children (condition, stmtList)\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		Boolean loopCondition = false;
		
		if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
			String message = "WhileStatement: 1st child is not a Boolean expression\n";
			message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
			throw new Exception(message);
		}
		loopCondition = (Boolean) interpret(children.get(0));
		while (loopCondition) {
			List<AtsASTNode> statementList = children.get(1).getOutgoingNodes();
			secondLoop:
				for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (m_flow != Flow.NORMAL) {
						switch (m_flow) {
						case BREAK:
						case RETURN: {
							m_flow = Flow.NORMAL;
							return null;
						}
						case CONTINUE: {
							m_flow = Flow.NORMAL;
							break secondLoop;
						}
						}
					}
				}
			loopCondition = (Boolean) interpret(children.get(0));
		}
		
		return null;
	}

	
	/**
	 * 
	 * @return A string which has all the test cases and their results.
	 */
	private String getTestCasesSummary() {
		StringBuilder builder = new StringBuilder();
		builder.append("----------------- Test Summary -----------------\n");
		for (int i = 0; i < m_testCases.size(); i++) {
			builder.append((i+1) + ". " + m_testCases.get(i).getAssertionSummary() + "\n");
		}
		return builder.toString();
	}
	
	/***
	 * Checks if the given automaton has the operation op.
	 * @param automaton The automaton on which the operation should be called
	 * @param op The name of the operation which should be called on the automaton
	 * @return The method object if the given automaton has the operation, otherwise null.
	 */
	private Method hasOperation(Object automaton, String op) {
		for (Method m : automaton.getClass().getMethods()) {
			if (m.getName().equalsIgnoreCase(op)) {
				return m;
			}
		}
		return null;
	}
	
	@SuppressWarnings("unchecked")
	private IOperation getAutomataOperation(String opName, ArrayList<Object> arguments) {
		
		if (opName.equalsIgnoreCase("accepts")) {
			NestedWordAutomaton<String, String> nwa = null;
			NestedWord<String> nw = null;
			if (arguments.size() != 2) {
				s_Logger.error("The operation \"accepts\" should have exactly 2 arguments, ");
				s_Logger.error("but it has  " + arguments.size() + " arguments.");
				return null;
			}
			if (arguments.get(0) instanceof INestedWordAutomaton) {
			   nwa = (NestedWordAutomaton<String, String>) arguments.get(0);
			}
			if (arguments.get(1) instanceof NestedWord<?>) {
				nw = (NestedWord<String>) arguments.get(1);
			}
			return new Acceptance<String, String>(nwa, nw, false, false);
		} else if (opName.equalsIgnoreCase("complement")) {
			if (arguments.size() != 1) {
				// TODO: Print some error message
				return null;
			}
			NestedWordAutomaton<String, String> nwa = null;
			if (arguments.get(0) instanceof INestedWordAutomaton) {
				nwa = (NestedWordAutomaton<String, String>) arguments.get(0);
			}
			try {
				return (new Complement<String, String>()).new ComplementSadd(nwa);
			} catch (OperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		} else if (opName.equalsIgnoreCase("intersect")) {
			if (arguments.size() != 2) {
				// TODO: Print error message
				return null;
			}
			NestedWordAutomaton<String, String> nwa1 = null;
			NestedWordAutomaton<String, String> nwa2 = null;
			if (arguments.get(0) instanceof INestedWordAutomaton) {
				nwa1 = (NestedWordAutomaton<String, String>) arguments.get(0);
			}
			if (arguments.get(1) instanceof INestedWordAutomaton) {
				nwa2 = (NestedWordAutomaton<String, String>) arguments.get(1);
			}
			try {
				return new Intersect<String, String>(false, true, nwa1, nwa2);
			} catch (OperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return null;
	}
	
	
}
