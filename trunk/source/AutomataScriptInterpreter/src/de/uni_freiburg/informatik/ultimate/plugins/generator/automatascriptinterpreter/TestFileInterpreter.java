package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.io.File;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.FileLocator;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AssignmentExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BreakStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanOperator;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConstantExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ContinueStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ForStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfElseStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedLassoword;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.Nestedword;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.OperationInvocationExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.RelationalExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.StatementList;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.WhileStatement;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;


enum Flow {
	NORMAL, BREAK, CONTINUE, RETURN;
}
public class TestFileInterpreter {
	
	class AutomataScriptTypeChecker {
		
		public void checkType(AtsASTNode n) throws IllegalArgumentException {
			if (n instanceof AssignmentExpression) {
				AssignmentExpression as = (AssignmentExpression) n;
				List<AtsASTNode> children = as.getOutgoingNodes();
				if (children.size() != 2) {
					String message = as.getLocation().getStartLine() + ": AssignmentExpression: It should have 2 operands\n";
					message = message.concat("On the left-hand side there  must be a VariableExpression, ");
					message = message.concat("On the right-hand side there can be an arbitrary expression.");
					throw new IllegalArgumentException(message);
				}
				VariableExpression var = (VariableExpression) children.get(0);
				// Check for correct types
				if (!var.isTypeCorrect(getType(children.get(1)))) {
					String message = "AssignmentExpression: Type error";
					message = message.concat(children.get(1).getReturnType() + " is not assignable to " + var.getReturnType());
					throw new IllegalArgumentException(message);
				}
			} else if (n instanceof BinaryExpression) {
				BinaryExpression be = (BinaryExpression) n;
				List<AtsASTNode> children = be.getOutgoingNodes();
				if (children.size() != 2) {
					String message = be.getLocation().getStartLine() + ": BinaryExpression should always have 2 children!\nNum of children: " + children.size();
					throw new IllegalArgumentException(message);
				}
				// Check for correct types
				if (!be.isTypeCorrect(getType(children.get(0)))) {
					String message = be.getLocation().getStartLine() + ": BinaryExpression: Left operand \n";
					message = message.concat("Expected: " + be.getReturnType() + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				} else if (!be.isTypeCorrect(getType(children.get(1)))) {
					String message = be.getLocation().getStartLine() + ": BinaryExpression: Right operand\n";
					message = message.concat("Expected: " + be.getReturnType() + "\tGot: " + children.get(1).getReturnType());
					throw new IllegalArgumentException(message);
				}
			}  else if (n instanceof ConditionalBooleanExpression) {
				ConditionalBooleanExpression cbe = (ConditionalBooleanExpression)n;
				List<AtsASTNode> children = cbe.getOutgoingNodes();
				if ((cbe.getOperator() == ConditionalBooleanOperator.NOT) && (children.size() != 1)) {
					String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: NOT operator should have 1 operand!\nNum of operands: " + children.size();
					throw new IllegalArgumentException(message);
				} else if ((cbe.getOperator() == ConditionalBooleanOperator.AND) && (children.size() != 2)) {
					String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: AND operator should have 2 operands!\nNum of operands: " + children.size();
					throw new IllegalArgumentException(message);
				} else if ((cbe.getOperator() == ConditionalBooleanOperator.OR) && (children.size() != 2)) {
					String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: OR operator should have 2 operands!\nNum of operands: " + children.size();
					throw new IllegalArgumentException(message);
				}
				// Check for correct types
				if (!cbe.isTypeCorrect(getType(children.get(0)))) {
					String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: 1st child is not a Boolean expression\n";
					message = message.concat("Expected: " + cbe.getReturnType() + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				}
				if ((children.size() == 2) && (!cbe.isTypeCorrect(getType(children.get(1))))) {
					String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: 2nd child\n";
					message = message.concat("Expected: " + cbe.getReturnType() + "\tGot: " + children.get(1).getReturnType());
					throw new IllegalArgumentException(message);
				}
			} else if (n instanceof ForStatement) {
				ForStatement fs = (ForStatement)n;
				List<AtsASTNode> children = fs.getOutgoingNodes();
				if (children.size() != 4) {
					String message = fs.getLocation().getStartLine() + ": ForStatement should have 4 children (condition, initStmt, updateStmt, stmtList)\n";
					message = message.concat("Num of children: " + children.size());
					throw new IllegalArgumentException(message);
				}
				if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
					String message = fs.getLocation().getStartLine() + ": ForStatement: Loopcondition is not a Boolean expression\n";
					message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				}
			} else if (n instanceof IfElseStatement) {
				IfElseStatement is = (IfElseStatement) n;
				List<AtsASTNode> children = is.getOutgoingNodes();
				if (children.size() != 3) {
					String message = is.getLocation().getStartLine() + ": IfElseStatement should have 3 children (Condition, Thenstatements, Elsestatements)";
					message = message.concat("Num of children: " + children.size());
					throw new IllegalArgumentException(message);
				}
				// Check for correct types
				if (children.get(0).getReturnType() != Boolean.class) {
					String message = is.getLocation().getStartLine() + ": IfElseStatement: Condition is not a Boolean expression\n";
					message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				}
			} else if (n instanceof IfStatement) {
				IfStatement is = (IfStatement) n;
				List<AtsASTNode> children = is.getOutgoingNodes();
				if (children.size() != 2) {
					String message = is.getLocation().getStartLine() + ": IfStatement should have 2 children (condition, thenStatements)\n";
					message = message.concat("Num of children: " + children.size());
					throw new IllegalArgumentException(message);
				}
				if (children.get(0).getReturnType() != Boolean.class) {
					String message = is.getLocation().getStartLine() + ": IfStatement: 1st child is not a Boolean expression\n";
					message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				}
			} else if (n instanceof OperationInvocationExpression) {
//				result = interpret((OperationInvocationExpression) n);
			} else if (n instanceof RelationalExpression) {
				RelationalExpression re = (RelationalExpression)n;
				List<AtsASTNode> children = re.getOutgoingNodes();
				if (children.size() != 2) {
					String message = re.getLocation().getStartLine() + ": RelationalExpression should always have 2 operands!\nNum of operands: " + children.size();
					throw new IllegalArgumentException(message);
				}
				// Check for correct types
				if (!children.get(0).isTypeCorrect(re.getExpectingType())) {
					String message = re.getLocation().getStartLine() + ": RelationalExpression: Left operand\n";
					message = message.concat("Expected: " + re.getExpectingType() + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				} else if (!children.get(1).isTypeCorrect(re.getExpectingType())) {
					String message = re.getLocation().getStartLine() + ": RelationalExpression: Right operand\n";
					message = message.concat("Expected: " + re.getExpectingType() + "\tGot: " + children.get(1).getReturnType());
					throw new IllegalArgumentException(message);
				}
			} else if (n instanceof StatementList) {
				for (AtsASTNode stmt : ((StatementList)n).getOutgoingNodes()) {
					checkType(stmt);
				}
			} else if (n instanceof UnaryExpression) {
				UnaryExpression ue = (UnaryExpression) n;
				List<AtsASTNode> children = ue.getOutgoingNodes();
				if (children.size() != 1) {
					String message = ue.getLocation().getStartLine() + ": UnaryExpression at line should always have 1 child!\nNum of children: " + children.size();
					throw new IllegalArgumentException(message);
				}
				if (!(children.get(0) instanceof VariableExpression)) {
					String message = ue.getLocation().getStartLine() + ": Unary operators are applicable only on variables!\nYou want to apply it on " + children.get(0).getClass().getSimpleName();
					throw new IllegalArgumentException(message);
				}
				// Check for correct types
				if (!children.get(0).isTypeCorrect(ue.getReturnType())) {
					String message = ue.getLocation().getStartLine() + ": UnaryExpression: 1st child\n";
					message = message.concat("Expected: " + ue.getReturnType() + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				}
			} else if (n instanceof VariableDeclaration) {
				VariableDeclaration vd = (VariableDeclaration) n;
				List<AtsASTNode> children = vd.getOutgoingNodes();
		    	if ((children.size() != 0) && (children.size() != 1)) {
		    		String message = vd.getLocation().getStartLine() + ": VariableDeclaration should have 0 or 1 child. (the value to assign)";
					throw new IllegalArgumentException(message);
		    	}
		    	if (!vd.isTypeCorrect(getType(children.get(0)))) {
		    		String message = vd.getLocation().getStartLine() + ": VariableDeclaration Typecheck error."
		    				           + " Expression on the right side should have type " + vd.getExpectingType().getSimpleName();
		    		throw new IllegalArgumentException(message);
		    	}
			} else if (n instanceof WhileStatement) {
				WhileStatement ws = (WhileStatement) n;
				List<AtsASTNode> children = ws.getOutgoingNodes();
				if (children.size() != 2) {
					String message = "WhileStatement should have 2 child nodes (condition, stmtList)\n";
					message = message.concat("Number of children: " + children.size());
					throw new IllegalArgumentException(message);
				}
				if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
					String message = "WhileStatement: Loop condition is not a Boolean expression\n";
					message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
					throw new IllegalArgumentException(message);
				}
			}
		}
		
		private Class<?> getType(AtsASTNode n) throws UnsupportedOperationException {
			if (n instanceof OperationInvocationExpression) {
				OperationInvocationExpression oe = (OperationInvocationExpression) n;
				String opName = oe.getOperationName().toLowerCase();
				if (m_existingOperations.containsKey(opName)) {
					Class<?> operationClass = m_existingOperations.get(opName);
					for (Class<?> interFace : operationClass.getInterfaces()) {
						if (interFace.equals(IOperation.class)) {
							for (Method m : operationClass.getMethods()) {
								if (m.getName().equals("getResult")) {
									return m.getReturnType();
								}
							}
							throw new UnsupportedOperationException("Operation \"" + opName + "\" has no operation \"getResult()\"");
						}
					}
				} else {
					throw new UnsupportedOperationException("Operation \"" + opName + "\" was not found!");
				}
				return null;
			} else {
				return n.getReturnType();
			}
		}
	}
	
	private Map<String, Object> m_variables;
	private Map<String, Class<?>> m_existingOperations;
	private Map<String, String> m_operationNamesToCorrectClassNames;
	private Flow m_flow;
	private AutomataDefinitionInterpreter m_automInterpreter;
	private AutomataScriptTypeChecker m_tChecker;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private List<GenericResult<Integer>> m_testCases;
	
	
	
	public TestFileInterpreter() {
		m_variables = new HashMap<String, Object>();
		m_flow = Flow.NORMAL;
		m_automInterpreter = new AutomataDefinitionInterpreter();
		m_testCases = new ArrayList<GenericResult<Integer>>();
		m_tChecker = new AutomataScriptTypeChecker();
		m_existingOperations = getOperationClasses();
		m_operationNamesToCorrectClassNames = new HashMap<String, String>();
		m_operationNamesToCorrectClassNames.put("accepts", "Acceptance");
//		m_operationNamesToCorrectClasses.put("accepts", "Acceptance");
		m_operationNamesToCorrectClassNames.put("complement", "Complement$ComplementDD");
		m_operationNamesToCorrectClassNames.put("complementsadd", "Complement$ComplementSadd");
		// m_operationNamesToCorrectClasses.put("intersect", "Intersect");
		// m_operationNamesToCorrectClasses.put("intersectNodd", "IntersectNodd");
		// m_operationNamesToCorrectClasses.put("difference", "Difference");
		// m_operationNamesToCorrectClasses.put("differenceSenwa", "DifferenceSenwa");
//		m_operationNamesToCorrectClasses.put("superDifference", "SuperDifference");
//		m_operationNamesToCorrectClasses.put("differenceSadd", "DifferenceSadd");
//		m_operationNamesToCorrectClasses.put("determinizeSadd", "DeterminizeSadd");
		m_operationNamesToCorrectClassNames.put("buchireduce", "ReduceBuchi");
		m_operationNamesToCorrectClassNames.put("buchiintersect", "Intersect");
		m_operationNamesToCorrectClassNames.put("finiteAutomaton", "PetriNet2FiniteAutomaton");
//		m_operationNamesToCorrectClasses.put("accepts", "Acceptance");
//		m_operationNamesToCorrectClasses.put("accepts", "Acceptance");
//		m_operationNamesToCorrectClasses.put("accepts", "Acceptance");
//		m_operationNamesToCorrectClasses.put("accepts", "Acceptance");
//		m_operationNamesToCorrectClasses.put("accepts", "Acceptance");
		
//		m_operationNamesToCorrectClasses.put("reachablestatescopy", "ReachableStatesCopy");
		m_operationNamesToCorrectClassNames.put("senwa", "SenwaBuilder");
	}
	
	public Object interpretTestFile(AtsASTNode node) throws Exception {
		List<AtsASTNode> children = node.getOutgoingNodes();
		if (children.size() != 2) {
			s_Logger.warn("AtsASTNode should have 2 children!");
			s_Logger.warn("It has: " + children.size() + " children.");
		}
		
		// Interpret automata definitions, if the file contains any.
		if (children.get(1) instanceof AutomataDefinitions) {
			m_automInterpreter.interpret((AutomataDefinitions) children.get(1));
		}
		
		m_variables.putAll(m_automInterpreter.getAutomata());
		// Type checking
		try {
			m_tChecker.checkType(children.get(0));
		} catch (IllegalArgumentException ie) {
			s_Logger.error("Typecheck error! Testfile won't be interpreted.");
			return null;
		}
		Object result = interpret(children.get(0));
		reportResult();
		return result;

	}
	
	private <T> Object interpret(AssignmentExpression as) throws Exception {
		List<AtsASTNode> children = as.getOutgoingNodes();
//		if (children.size() != 2) {
//			String message = as.getLocation().getStartLine() + ": AssignmentExpression: It should have 2 operands\n";
//			message = message.concat("On the left-hand side there  must be a VariableExpression, ");
//			message = message.concat("On the right-hand side there can be an arbitrary expression.");
//			throw new RuntimeException(message);
//		}
		VariableExpression var = (VariableExpression) children.get(0);
		if (!m_variables.containsKey(var.getIdentifier())) {
			String message = as.getLocation().getStartLine() + ": AssignmentExpression: Variable " + var.getIdentifier() + " was not declared before.";
			throw new Exception(message);
		}
		Object oldValue = m_variables.get(var.getIdentifier());
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
		Integer v1 = (Integer) interpret(children.get(0));
		Integer v2 = (Integer) interpret(children.get(1));
		
		switch(be.getOperator()) {
		case PLUS: return v1 + v2;
		case MINUS: return v1 - v2;
		case MULTIPLICATION: return v1 * v2;
		case DIVISION: return v1 / v2;
		default: throw new UnsupportedOperationException(be.getLocation().getStartLine() + ": BinaryExpression: This type of operator is not supported: " + be.getOperator());
		}
	}
	
	private <T> Object interpret(BreakStatement bst) throws Exception {
		List<AtsASTNode> children = bst.getOutgoingNodes();
		if (children.size() != 0) {
			String message = bst.getLocation().getStartLine() + ": BreakStatement: Should not have any children.\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		
		// Change the flow
		m_flow = Flow.BREAK;
		return null;
	}
	
	private <T> Boolean interpret(ConditionalBooleanExpression cbe) throws Exception{
		List<AtsASTNode> children = cbe.getOutgoingNodes();
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
			String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: This type of operator is not supported: " + cbe.getOperator();
	    	throw new UnsupportedOperationException(message);  
	      }
		}
	}

	private <T> Object interpret(ConstantExpression ce) {
		return ce.getValue();
	}
	
	private <T> Object interpret(ContinueStatement cst) throws Exception {
		List<AtsASTNode> children = cst.getOutgoingNodes();
		if (children.size() != 0) {
			String message = cst.getLocation().getStartLine() + ": ContinueStatement: Should not have any children.\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		// Change the flow
		m_flow  =  Flow.CONTINUE;
		return null;
	}
	
	private <T> Object interpret(ForStatement fs) throws Exception {
		List<AtsASTNode> children = fs.getOutgoingNodes();
		
		Boolean loopCondition = false;
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
		
		// children(0) is the condition
		if ((Boolean) interpret(children.get(0))) {
			interpret(children.get(1));
		} else {
			interpret(children.get(2));
		}
		return null;
	}
	
	private <T> Object interpret(IfStatement is) throws Exception {
		List<AtsASTNode> children = is.getOutgoingNodes();
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
		throw new UnsupportedOperationException("interpret(NestedLassoWord) not yet implemented!");
	}
	
	private <T> Object interpret(OperationInvocationExpression oe) throws Exception {
		List<AtsASTNode> children = oe.getOutgoingNodes();
		if (children.size() != 1) {
			String message = oe.getLocation().getStartLine() + ": OperationExpression should have only 1 child (ArgumentList)";
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

		Object result = null;

		if (oe.getOperationName().equalsIgnoreCase("assert") && arguments.size() == 1) {
			result = arguments.get(0);
			if (result instanceof Boolean) {
				if ((Boolean) result) {
					m_testCases.add(new GenericResult<Integer>(oe.getLocation().getStartLine(), 
									Activator.s_PLUGIN_ID, 
							        null,
							        oe.getLocation(), 
							        "Assertion holds.", 
							        "long", 
							        Severity.INFO));
				} else {
					m_testCases.add(new GenericResult<Integer>(oe.getLocation().getStartLine(), 
									Activator.s_PLUGIN_ID, 
									null,
									oe.getLocation(), 
									"Assertion violated!", 
									"long", 
									Severity.ERROR));
				}
			}
		} else if (oe.getOperationName().equalsIgnoreCase("print")) {
			for (Object o : arguments) {
				s_Logger.info(o.toString());
			}
			
		} else {
			IOperation op = getAutomataOperation(oe.getOperationName(), arguments);
			if (op != null) {
				result = op.getResult();
			} 
		}
		return result;
	}
	
	private <T> Boolean interpret(RelationalExpression re) throws Exception{
		List<AtsASTNode> children = re.getOutgoingNodes();
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
			default: throw new UnsupportedOperationException(re.getLocation().getStartLine() + ": RelationalExpression: This type of operator is not supported: " + re.getOperator());
			}
		}
		return null;
	}
	
	private <T> Object interpret(ReturnStatement rst) throws Exception {
		List<AtsASTNode> children = rst.getOutgoingNodes();
		if ((children.size() != 0) && (children.size() != 1)) {
			String message = rst.getLocation().getStartLine() + ": ReturnStatement: Too many children\n";
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
	    	String message =  ue.getLocation().getStartLine() + ": UnaryExpression: This type of operator is not supported: " + ue.getOperator(); 
	    	throw new UnsupportedOperationException(message);  
	      }
	      }
		}
	
    private <T> Object interpret(VariableDeclaration vd) throws Exception {
    	List<AtsASTNode> children = vd.getOutgoingNodes();
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
			String message = "VariableExpression: Variable " + ve.getIdentifier() + " at line " + ve.getLocation().getStartLine() + " was not declared.";
			throw new RuntimeException(message);
		}
		
		return m_variables.get(ve.getIdentifier());
	}
	
	private <T> Object interpret(WhileStatement ws) throws Exception {
		List<AtsASTNode> children = ws.getOutgoingNodes();
		Boolean loopCondition = (Boolean) interpret(children.get(0));
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

	private void reportResult() {
		StringBuilder builder = new StringBuilder();
		builder.append("----------------- Test Summary -----------------\n");
		String testCasesSummary = "All testcases passed.";
		for (GenericResult<Integer> test : m_testCases) {
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, test);
			switch (test.getSeverity()) {
			case ERROR: {s_Logger.error("Line " + test.getLocation().getStartLine() + ": " + test.getShortDescription());
			             testCasesSummary = "Some testcases failed."; } break;
			case INFO: s_Logger.info("Line " + test.getLocation().getStartLine() + ": " + test.getShortDescription()); break;
			default: s_Logger.error("Error: " + test.getShortDescription());
			}
		}
		// Report summary of the testcases
		s_Logger.info(testCasesSummary);
	}

	private IOperation getAutomataOperation(String opName, ArrayList<Object> arguments) {
		String operationName = opName.toLowerCase();
		IOperation result = null;
		if (!m_existingOperations.containsKey(operationName)) {
			if (m_operationNamesToCorrectClassNames.containsKey(operationName)) {
				operationName = m_operationNamesToCorrectClassNames.get(operationName).toLowerCase();
			}
		}
		if (m_existingOperations.containsKey(operationName)) {
			Class<?> operationClass = m_existingOperations.get(operationName);
			Class<?>[] implementedInterfaces = operationClass.getInterfaces();
			for (Class<?> interFace : implementedInterfaces) {
				if (interFace.equals(IOperation.class)) {
					Constructor<?>[] operationConstructors = operationClass.getConstructors();
					for (Constructor<?> c : operationConstructors) {
						if (allArgumentsHaveCorrectTypeForThisConstructor(c, arguments)) {
							try {
								result = (IOperation) c.newInstance(arguments.toArray());
								return result;
							} catch (InstantiationException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							} catch (IllegalAccessException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							} catch (IllegalArgumentException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							} catch (InvocationTargetException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}
					}					
				}
			}
			
		}
		
		return result;
	}
	
	
	private boolean allArgumentsHaveCorrectTypeForThisConstructor(Constructor<?> c, List<Object> arguments) {
		int i = 0;
		int minArgSize = (c.getParameterTypes().length > arguments.size() ? arguments.size() : c.getParameterTypes().length);
		for (Class<?> type : c.getParameterTypes()) {
			if ((i >= minArgSize) || !(type.isAssignableFrom(arguments.get(i).getClass()))) {
				return false;
			}
			++i;
		}
		return true;
	}
	

	/**
	 * 
	 * @return Returns a map from String to class objects from the classes found in the directories.
 	 */
	private static Map<String, Class<?>> getOperationClasses() {
		Map<String, Class<?>> result = new HashMap<String, Class<?>>();
		String baseDir = "/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/operations";
		String[] dirs = { "", "buchiReduction" };
		for (String dir : dirs) {
			String[] files = filesInDirectory(baseDir + "/" + dir);
			for (String file : files) {
				if (file.endsWith(".class")) {
					String fileWithoutSuffix = file.substring(0, file.length()-6);
					String baseDirInPackageFormat = baseDir.replaceAll("/", ".");
					if (baseDirInPackageFormat.charAt(0) == '.') {
						baseDirInPackageFormat = baseDirInPackageFormat.substring(1);
					}
					String path = baseDirInPackageFormat + "." + fileWithoutSuffix;
					Class<?> clazz = null;
					try {
						clazz = Class.forName(path);
					} catch (ClassNotFoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
						s_Logger.error("Couldn't load/find class " + path);
						break;
					}
					String operationName = fileWithoutSuffix.toLowerCase();
					result.put(operationName, clazz);
				}
			}
		}
		return result;
	}
	
	
	/**
	 * Return the filenames of the files in the folder
	 * /resources/examples/ + dirSuffix (path given relative to root of this
	 * package).
	 * 
	 * We use the classloader to get the URL of this folder. We support only
	 * URLs with protocol <i>file</i> and <i>bundleresource</i>.
	 * At the moment these are the only ones that occur in Website and
	 * WebsiteEclipseBridge.
	 */
	private static String[] filesInDirectory(String dir) {
		URL dirURL = IOperation.class.getClassLoader().getResource(dir);
		if (dirURL == null) {
			throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
		}
		String protocol = dirURL.getProtocol();
		File dirFile = null;
		if (protocol.equals("file")) {
			try {
				dirFile = new File(dirURL.toURI());
			} catch (URISyntaxException e) {
				e.printStackTrace();
				throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
			}
		} else if (protocol.equals("bundleresource")) {
			try {
				URL fileURL = FileLocator.toFileURL(dirURL);
				dirFile = new File(fileURL.toURI());
			} catch (Exception e) {
				e.printStackTrace();
				throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
			}
		} else {
			throw new UnsupportedOperationException("unknown protocol");
		}
		String[] files = dirFile.list();
		return files;
	}
	
}
