package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.net.URL;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


import org.apache.log4j.Logger;
import org.eclipse.core.runtime.FileLocator;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AssignmentExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BinaryExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BreakStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanOperatorAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConstantExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ContinueStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ForStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfElseStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedLassowordAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.OperationInvocationExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.RelationalExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ReturnStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.StatementListAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.UnaryExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableDeclarationAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.WhileStatementAST;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;


/**
 * This enum represents the current flow of the program.
 * It could have the values "NORMAL", "BREAK", "CONTINUE", and
 * "RETURN". It is necessary to implement the "continue" and "break"
 * function for loops.
 * @author musab@informatik.uni-freiburg.de
 *
 */
enum Flow {
	NORMAL, BREAK, CONTINUE, RETURN;
}


/**
 * This is the main class for interpreting automata script test files.
 * It fulfills the following tasks:
 * - Interpreting automata definitions
 * - Type checking the automata script test file
 * - Interpreting the automata script test file
 * - Generation and output of the results
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class TestFileInterpreter {
	
	/**
	 * This class implements a static type checker for the automatascript files.
	 * @author musab@informatik.uni-freiburg.de
	 *
	 */
	class AutomataScriptTypeChecker {
		/**
		 * A map from variable names to the type they represent. This is needed to check
		 * for type conformity, e.g. variable assignment.
		 */
		private Map<String, Class<?>> m_localVariables = new HashMap<String, Class<?>>();
		
		/**
		 * Checks the test file for type errors and for
		 * undeclared variables.
		 * @param n the root node of the AST 
		 * @throws InterpreterException
		 */
		public void checkTestFile(AtsASTNode n) throws InterpreterException {
			for (Map.Entry<String, Object > entry : m_variables.entrySet()) {
				m_localVariables.put(entry.getKey(), entry.getValue().getClass());
			}
			checkType(n);
		}
		
		private void checkType(AtsASTNode n) throws InterpreterException {
			if (n instanceof AssignmentExpressionAST) {
				checkType((AssignmentExpressionAST) n);
			} else if (n instanceof BinaryExpressionAST) {
				checkType((BinaryExpressionAST) n);
			}  else if (n instanceof ConditionalBooleanExpressionAST) {
				checkType((ConditionalBooleanExpressionAST) n);
			} else if (n instanceof ForStatementAST) {
				checkType((ForStatementAST) n);
			} else if (n instanceof IfElseStatementAST) {
				checkType((IfElseStatementAST) n);
			} else if (n instanceof IfStatementAST) {
				checkType((IfStatementAST) n);
			} else if (n instanceof OperationInvocationExpressionAST) {
				checkType((OperationInvocationExpressionAST) n);
			} else if (n instanceof RelationalExpressionAST) {
				checkType((RelationalExpressionAST) n);
			} else if (n instanceof StatementListAST) {
				for (AtsASTNode stmt : ((StatementListAST)n).getOutgoingNodes()) {
					checkType(stmt);
				}
			} else if (n instanceof UnaryExpressionAST) {
				checkType((UnaryExpressionAST) n);
			} else if (n instanceof VariableDeclarationAST) {
				checkType((VariableDeclarationAST) n);
			} else if (n instanceof VariableExpressionAST) {
				checkType((VariableExpressionAST) n);
			} else if (n instanceof WhileStatementAST) {
				checkType((WhileStatementAST) n);
			}
				
		}
		
		private void checkType(AssignmentExpressionAST as) throws InterpreterException {
			List<AtsASTNode> children = as.getOutgoingNodes();
			ILocation errorLocation = as.getLocation();
			if (children.size() != 2) {
				String message = "Assignment should have 2 operands." + System.getProperty("line.separator");
				message = message.concat("On the left-hand side there  must be a variable, ");
				message = message.concat("on the right-hand side there can be an arbitrary expression.");
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check the type of children
			checkType(children.get(0));
			checkType(children.get(1));
			
			VariableExpressionAST var = (VariableExpressionAST) children.get(0);
			// Check whether the right-hand side has expected type.
			for (Class<?> c : getTypes(children.get(1))) {
				children.get(1).setType(c);
				// Check for correct types
				if (AssignableTest.isAssignableFrom(var.getReturnType(), c)) {
					return;
				}
			}
			String message = "Right side has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + var.getReturnType().getSimpleName() + "\tGot: " +
					  children.get(1).getReturnType().getSimpleName() + "");
			String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
			
		}
		
		private void checkType(BinaryExpressionAST be)  throws InterpreterException {
			List<AtsASTNode> children = be.getOutgoingNodes();
			ILocation errorLocation = be.getLocation();
			if (children.size() != 2) {
				String message = be.getOperatorAsString() + " should have 2 operands of type \"int\"." +
				                 System.getProperty("line.separator") + "Num of operands: " + children.size();
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check children for correct type
			checkType(children.get(0));
			checkType(children.get(1));
			
			// If the return type of this binary expression is 'String', we do not need to type check the operands
			// because we just call the toString-Method of every operand.
			if (be.getReturnType() == String.class) {
				return;
			}
			
			// Check whether first child has expected type.
			boolean firstChildHasCorrectType = false;
			for (Class<?> c : getTypes(children.get(0))) {
				if (AssignableTest.isAssignableFrom(be.getReturnType(), c)) {
					firstChildHasCorrectType = true;
				}
			}
			
			if(!firstChildHasCorrectType) {
				String message = "Left operand of \"" + be.getOperatorAsString() + "\" has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + be.getReturnType().getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			
			// Check whether second child has expected type.
			for (Class<?> c : getTypes(children.get(1))) {
				if (AssignableTest.isAssignableFrom(be.getReturnType(), c)) {
					return;
				}
			}
			String message = "Right operand of \"" + be.getOperatorAsString() + "\" has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + be.getReturnType().getSimpleName() + "\tGot: " + children.get(1).getReturnType().getSimpleName() + "");
			String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		
		private void checkType(ConditionalBooleanExpressionAST cbe) throws InterpreterException {
			List<AtsASTNode> children = cbe.getOutgoingNodes();
			ILocation errorLocation = cbe.getLocation();
			if ((cbe.getOperator() == ConditionalBooleanOperatorAST.NOT) && (children.size() != 1)) {
				String message = "\"!\" operator should have 1 operand." + System.getProperty("line.separator") + "Num of operands: " + children.size();
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			} else if ((cbe.getOperator() == ConditionalBooleanOperatorAST.AND) && (children.size() != 2)) {
				String message = "\"&&\" operator should have 2 operands." + System.getProperty("line.separator") + "Num of operands: " + children.size();
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			} else if ((cbe.getOperator() == ConditionalBooleanOperatorAST.OR) && (children.size() != 2)) {
				String message = " \"||\" operator should have 2 operands." + System.getProperty("line.separator") + "Num of operands: " + children.size();
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check children for correct type
			checkType(children.get(0));
			if (children.size() == 2) checkType(children.get(1));
			// Check whether first child has type 'int'
			boolean firstChildHasCorrectType = false;
			for (Class<?> c : getTypes(children.get(0))) {
				if (AssignableTest.isAssignableFrom(cbe.getReturnType(), c)) {
					firstChildHasCorrectType = true;
				}
			}
			if (!firstChildHasCorrectType) {
				String message = (children.size() == 2 ? "Left " : "") + "argument has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + cbe.getReturnType().getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check whether second child has type 'int'
			if (children.size() == 2) {
				for (Class<?> c : getTypes(children.get(1))) {
					if (AssignableTest.isAssignableFrom(cbe.getReturnType(), c)) {
						return;
					}
				}
				String message = "Right argument has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + cbe.getReturnType().getSimpleName() + "\tGot: " + children.get(1).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		private void checkType(ForStatementAST fs)  throws InterpreterException {
			List<AtsASTNode> children = fs.getOutgoingNodes();
			ILocation errorLocation = fs.getLocation();
			if (children.size() != 4) {
				String message = "ForStatement should have 4 arguments (initStmt, condition, updateStmt) {stmtList}." + System.getProperty("line.separator");
				message = message.concat("Num of children: " + children.size());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// First child is the loop condition.
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = "Loopcondition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		private void checkType(IfElseStatementAST is)  throws InterpreterException {
			List<AtsASTNode> children = is.getOutgoingNodes();
			ILocation errorLocation = is.getLocation();
			if (children.size() != 3) {
				String message = "IfElseStatement should have 3 operands (Condition) { Thenstatements} {Elsestatements})" + System.getProperty("line.separator");
				message = message.concat("Num of operands: " + children.size());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check the children for correct type.
			checkType(children.get(0));
			// Check if the if-condition has type Boolean.
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		private void checkType(IfStatementAST is)  throws InterpreterException {
			List<AtsASTNode> children = is.getOutgoingNodes();
			ILocation errorLocation = is.getLocation();
			if (children.size() != 2) {
				String message = "IfStatement should have 2 operands (condition) {thenStatements}" +System.getProperty("line.separator");
				message = message.concat("Num of operands: " + children.size());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check the first child for correct type
			checkType(children.get(0));
			// Check if the if-condition has type Boolean.
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		private void checkType(OperationInvocationExpressionAST oe) throws InterpreterException {
			ILocation errorLocation = oe.getLocation();
			String opName = oe.getOperationName().toLowerCase();
			if (!m_existingOperations.containsKey(opName)) {
				if (!opName.equals("assert") && !opName.equals("print")) {
					String shortDescr = "Unsupported operation \"" + oe.getOperationName() + "\"";
					String shortDescription = shortDescr;
					String allOperations = (new ListExistingOperations(m_existingOperations)).prettyPrint();
					String longDescr = "We support only the following operations " + System.getProperty("line.separator") + allOperations;
					String longDescription = longDescr;
					throw new InterpreterException(errorLocation, shortDescription, longDescription);
				} 
			}
			// Check the arguments of this operation for correct type.
			if ((oe.getOutgoingNodes() != null) && (oe.getOutgoingNodes().get(0) != null)) {
				for (AtsASTNode n : oe.getOutgoingNodes().get(0).getOutgoingNodes()) {
					checkType(n);
				}
			}
			if (opName.equals("print")) return;
			/*
			 * Set type of this operation, because until now, it
			 * didn't have any type. It is not relevant for further
			 * type checking results, but it avoids NullPointerExceptions. 
			 */
			Set<Class<?>> types = getTypes(oe);
			if (!types.isEmpty()) {
				Class<?>[] arr = new Class<?>[1];
				arr = types.toArray(arr);
				oe.setType(arr[0]);
			}
			
		}
		
		private void checkType(RelationalExpressionAST re)  throws InterpreterException {
			List<AtsASTNode> children = re.getOutgoingNodes();
			ILocation errorLocation = re.getLocation();
			if (children.size() != 2) {
				String message = "\"" + re.getOperatorAsString() + " should have 2 operands." + System.getProperty("line.separator") + "Num of operands: "
				                 + children.size();
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check children for correct type
			checkType(children.get(0));
			checkType(children.get(1));
			// Check whether first child has expected type.
			boolean firstChildHasCorrectType = false;
			for (Class<?> c : getTypes(children.get(0))) {
				if (AssignableTest.isAssignableFrom(re.getExpectingType(), c)) {
					firstChildHasCorrectType = true;
				}
			}
			if (!firstChildHasCorrectType) {
				String message = "Left operand has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + re.getExpectingType().getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check whether second child has expected type.
			for (Class<?> c : getTypes(children.get(1))) {
				if (AssignableTest.isAssignableFrom(re.getExpectingType(), c)) {
					return;
				}
			}
			String message = "Right operand has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + re.getExpectingType().getSimpleName() + "\tGot: " + children.get(1).getReturnType().getSimpleName());
			String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		
		private void checkType(UnaryExpressionAST ue)  throws InterpreterException {
			List<AtsASTNode> children = ue.getOutgoingNodes();
			ILocation errorLocation = ue.getLocation();
			if (children.size() != 1) {
				String message = "\"" + ue.getOperatorAsString() + "\" should have one variable as argument." + System.getProperty("line.separator") + "Num of arguments: " + children.size();
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check children for correct type
			checkType(children.get(0));
			
			if (!(children.get(0) instanceof VariableExpressionAST)) {
				String message = "Unary operators are applicable only on variables." + System.getProperty("line.separator") + "You want to apply it on " + children.get(0).getClass().getSimpleName();
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check if variable has expected type, namely
			// type 'int'
			for (Class<?> c : getTypes(children.get(0))) {
				if (AssignableTest.isAssignableFrom(ue.getExpectingType(), c)) {
					return;
				}
			}
			String message = "Operand has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + ue.getExpectingType().getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
			String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		
		private void checkType(VariableExpressionAST v) throws InterpreterException {
			ILocation errorLocation = v.getLocation();
			if (m_localVariables.containsKey(v.getIdentifier())) {
				v.setType(m_localVariables.get(v.getIdentifier()));
			} else {
				String shortDescription = "Undeclared variable";
				String message = "Variable \"" + v.getIdentifier() + "\" at line " + v.getLocation().getStartLine() + " was not declared.";
				String longDescription = "Variable \"" + v.getIdentifier() + "\" was not declared.";
				throw new InterpreterException(errorLocation, shortDescription, longDescription);
			}
		}
		
		private void checkType(VariableDeclarationAST vd)  throws InterpreterException {
			List<AtsASTNode> children = vd.getOutgoingNodes();
			ILocation errorLocation = vd.getLocation();
	    	if ((children.size() != 0) && (children.size() != 1)) {
	    		String message = "Variabledeclaration can have at most one operand. (the value to assign)";
	    		String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
	    	}
	    	for (String id : vd.getIdentifiers()) {
	    		m_localVariables.put(id, vd.getExpectingType());
	    	}
	    	// if the variable doesn't get assigned a value, then return.
	    	if (children.size() == 0) return;
	    	
	    	// Check type of the right-hand side of the variable assignment.
	    	checkType(children.get(0));
	    	for (Class<?> c : getTypes(children.get(0))) {
	    		if (AssignableTest.isAssignableFrom(vd.getReturnType(), c)) {
	    			return;
	    		}
	    	}
	    	String message = "Operand on the right side has incorrect type." + System.getProperty("line.separator")
	    			+ "Expected: " + vd.getExpectingType().getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName();
	    	String longDescription = message;
	    	throw new InterpreterException(errorLocation, longDescription);
		}
		
		private void checkType(WhileStatementAST ws)  throws InterpreterException {
			List<AtsASTNode> children = ws.getOutgoingNodes();
			ILocation errorLocation = ws.getLocation();
			if (children.size() != 2) {
				String message = "WhileStatement should have 2 operands (condition) {stmtList}" + System.getProperty("line.separator");
				message = message.concat("Number of children: " + children.size());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		
		/**
		 * Returns the possible types for the given AST node. Only operations can
		 * potentially have more return types, because there could operations with
		 * different return types, but with the same name. 
		 * @param n the AtsAST node
		 * @return a set of types, where the set could contain more than 1 element
		 * if the given node represents an operation invocation, otherwise it contains
		 * only 1 element. 
		 * @throws UnsupportedOperationException if the operation was not found, or if the operation
		 * has no declared method called "getResult".
		 */
		private Set<Class<?>> getTypes(AtsASTNode n) throws UnsupportedOperationException {
			if (n instanceof OperationInvocationExpressionAST) {
				OperationInvocationExpressionAST oe = (OperationInvocationExpressionAST) n;
				String opName = oe.getOperationName().toLowerCase();
				Set<Class<?>> returnTypes = new HashSet<Class<?>>();
				if (opName.equals("print") || opName.equals("assert")) {
					return returnTypes;
				}
				if (m_existingOperations.containsKey(opName)) {
					Set<Class<?>> operationClasses = m_existingOperations.get(opName);
					for (Class<?> operationClass : operationClasses) {
							for (Method m : operationClass.getMethods()) {
								if (m.getName().equals("getResult")) {
									returnTypes.add(m.getReturnType());
								}
							}
					}
					if (returnTypes.isEmpty()) {
						throw new UnsupportedOperationException("Operation \"" + opName + "\" has no operation \"getResult()\"");
					} else {
						return returnTypes;
					}
				} else {
					throw new UnsupportedOperationException("Operation \"" + opName + "\" was not found!");
				}
			} else {
				Set<Class<?>> returnType = new HashSet<Class<?>>();
				returnType.add(n.getReturnType());
				return returnType;
			}
		}


	}
	
	/**
	 * Contains the declared variables, automata variables too. It is a map from
	 * variable name to the object it represents.
	 */
	private Map<String, Object> m_variables;
	/**
	 * Contains current existing automata operations. It is a map from
	 * operation name to a set of class types, because there might be operations
	 * with the same name, but with different parameter types and in different packages.
	 * e.g. Accepts for NestedWord automata and Accepts for Petri nets.
	 */
	private Map<String, Set<Class<?>>> m_existingOperations;
	/**
	 * The current flow of the program.
	 */
	private Flow m_flow;
	/**
	 * Our interpreter for automata definitions. 
	 */
	private AutomataDefinitionInterpreter m_automInterpreter;
	/**
	 * Our type checker for the automatascript file.
	 */
	private AutomataScriptTypeChecker m_tChecker;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	/**
	 * The automaton, which was lastly printed by a print operation. 
	 */
	private IAutomaton<?, ?> m_LastPrintedAutomaton;
	/**
	 * Indicates whether the automaton, which is output by a print operation, should
	 * also be printed to a .ats-file.
	 */
	private boolean m_printAutomataToFile = false;
	private PrintWriter m_printWriter;
	private String m_path = ".";
	public enum LoggerSeverity {INFO, WARNING, ERROR, DEBUG};
	
	private enum Finished {FINISHED, TIMEOUT, ERROR, OUTOFMEMORY};
	/**
	 * If an error occurred during the interpretation this is set to true
	 * and further interpretation is aborted.
	 */
	private final List<GenericResultAtElement<AtsASTNode>> m_ResultOfAssertStatements;
//	private boolean m_ErrorOccured = false;
	
	
	public TestFileInterpreter() {
		readPreferences();
		m_variables = new HashMap<String, Object>();
		m_flow = Flow.NORMAL;
		m_automInterpreter = new AutomataDefinitionInterpreter();
		m_tChecker = new AutomataScriptTypeChecker();
		m_existingOperations = getOperationClasses();
		m_LastPrintedAutomaton = null;
		m_ResultOfAssertStatements = new ArrayList<GenericResultAtElement<AtsASTNode>>();
		if (m_printAutomataToFile) {
			String path = m_path + File.separator + "automatascriptOutput" + getDateTime() + ".ats";
			File file = new File(path);
			try {
				FileWriter writer = new FileWriter(file);
				m_printWriter = new PrintWriter(writer);
			} catch (IOException e) {
				throw new AssertionError(e);
			}
		}
	}
	
	private void readPreferences() {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		m_printAutomataToFile = prefs.getBoolean(PreferenceInitializer.Name_WriteToFile);
		m_path = prefs.getString(PreferenceInitializer.Name_Path);
	}
	
	
	private static String getDateTime() {
        DateFormat dateFormat = new SimpleDateFormat("yyyyMMddHHmmss");
        Date date = new Date();
        return dateFormat.format(date);
    }
	
	/**
	 * Method to interpret an automatascript test file. The interpretation is done in 4 steps.
	 * Step 1: Interpret automata defintions.
	 * Step 2: Check the automatascript test file for correct types and undeclared variables. (Type checking)
	 * Step 3: Interpret the automatascript test file.
	 * Step 4: Report the results to the Logger and to the web interface.
	 * @param node the root node of the AST
	 * @return the result of the automatascript test file, which is either an automaton or null.
	 */
	public Object interpretTestFile(AtsASTNode node) {
		AutomataTestFileAST ats = null;
		if (node instanceof AutomataTestFileAST) {
			ats = (AutomataTestFileAST) node;
		}
		Finished interpretationFinished = Finished.FINISHED;
		reportToLogger(LoggerSeverity.DEBUG, "Interpreting automata definitions...");
		// Interpret automata definitions
		try {
			m_automInterpreter.interpret(ats.getAutomataDefinitions());
		} catch (Exception e) {
			reportToLogger(LoggerSeverity.INFO, "Error during interpreting automata definitions.");
			reportToLogger(LoggerSeverity.INFO, "Error: " + e.getMessage());
			reportToLogger(LoggerSeverity.INFO, "Interpretation of testfile cancelled.");
			reportToUltimate(Severity.ERROR, e.getMessage() + " Interpretation of testfile cancelled.", "Error", node);
			interpretationFinished = Finished.ERROR;
		}
		
		if (interpretationFinished == Finished.FINISHED) {
			// Put all defined automata into variables map
			m_variables.putAll(m_automInterpreter.getAutomata());
			reportToLogger(LoggerSeverity.DEBUG, "Typechecking of test file...");
			// Type checking
			try {
				m_tChecker.checkTestFile(ats.getStatementList());
			} catch (InterpreterException e) {
				reportToLogger(LoggerSeverity.INFO, "Error: " + e.getMessage());
				reportToLogger(LoggerSeverity.INFO,	"Interpretation of testfile cancelled.");
				String shortDescription = e.getShortDescription();
				if (shortDescription == null) {
					shortDescription = "Error";
				}
				reportToUltimate(Severity.ERROR, e.getLongDescription(), shortDescription, node);
				interpretationFinished = Finished.ERROR;
			}
		}

		Object result = null;
		if (interpretationFinished == Finished.FINISHED) {
			// Interpreting test file
			reportToLogger(LoggerSeverity.DEBUG, "Interpreting test file...");
			if (ats.getStatementList() == null) {
				// File contains only automata definitions no testcases.
				result = null;
			} else {
				try {
					result = interpret(ats.getStatementList());
				} catch (InterpreterException e) {
					if (e.getLongDescription().equals("Timeout")) {
						interpretationFinished = Finished.TIMEOUT;
					} else if (e.getLongDescription().equals("OutOfMemoryError")) {
						interpretationFinished = Finished.OUTOFMEMORY;
					} else {
						interpretationFinished = Finished.ERROR;
					}
					printMessage(Severity.ERROR, LoggerSeverity.INFO,
							e.getLongDescription(),
							"Interpretation of ats file failed",
							node);
				}
			}
		}
		reportToLogger(LoggerSeverity.DEBUG, "Reporting results...");
		reportResult(interpretationFinished);
		if (m_printAutomataToFile) {
			m_printWriter.close();
		}
		return result;
	}
	
	/**
	 * Gets the automaton which was lastly printed by a print-operation.
	 * @return
	 */
	public IAutomaton<?, ?> getLastPrintedAutomaton() {
		return m_LastPrintedAutomaton;
	}
	
	private Object interpret(AssignmentExpressionAST as) throws InterpreterException {
		List<AtsASTNode> children = as.getOutgoingNodes();
		VariableExpressionAST var = (VariableExpressionAST) children.get(0);
		if (!m_variables.containsKey(var.getIdentifier())) {
			String message = as.getLocation().getStartLine() + ": Variable \"" + var.getIdentifier() + "\" was not declared before.";
			throw new InterpreterException(as.getLocation(), message);
		}
		Object oldValue = m_variables.get(var.getIdentifier());
		Object newValue = interpret(children.get(1));
		
		if (newValue == null) {
			String longDescr = "Var \"" + var.getIdentifier() + "\" is assigned \"null\".";
			throw new InterpreterException(as.getLocation(),longDescr);
		}
		
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
			throw new InterpreterException(as.getLocation(), 
					"AssignmentExpression: This type of operator is not supported: " + as.getOperator());
		}
			
		}
		return oldValue;
	}
		
	private Object interpret(AtsASTNode node) throws InterpreterException {
		Object result = null;
		if (node instanceof AssignmentExpressionAST) {
			result = interpret((AssignmentExpressionAST) node);
		} else if (node instanceof BinaryExpressionAST) {
			result = interpret((BinaryExpressionAST) node);
		} else if (node instanceof BreakStatementAST) {
			result = interpret((BreakStatementAST) node);
		} else if (node instanceof ConditionalBooleanExpressionAST) {
			result = interpret((ConditionalBooleanExpressionAST) node);
		} else if (node instanceof ConstantExpressionAST) {
			result = interpret((ConstantExpressionAST) node);
		} else if (node instanceof ContinueStatementAST) {
			result = interpret((ContinueStatementAST) node);
		} else if (node instanceof ForStatementAST) {
			result = interpret((ForStatementAST) node);
		} else if (node instanceof IfElseStatementAST) {
			result = interpret((IfElseStatementAST) node);
		} else if (node instanceof IfStatementAST) {
			result = interpret((IfStatementAST) node);
		} else if (node instanceof NestedwordAST) {
			result = interpret((NestedwordAST) node);
		} else if (node instanceof NestedLassowordAST) {
			result = interpret((NestedLassowordAST) node);
		} else if (node instanceof OperationInvocationExpressionAST) {
			result = interpret((OperationInvocationExpressionAST) node);
		} else if (node instanceof RelationalExpressionAST) {
			result = interpret((RelationalExpressionAST) node);
		} else if (node instanceof ReturnStatementAST) {
			result = interpret((ReturnStatementAST) node);
		} else if (node instanceof StatementListAST) {
			result = interpret((StatementListAST) node);
		} else if (node instanceof UnaryExpressionAST) {
			result = interpret((UnaryExpressionAST) node);
		} else if (node instanceof VariableDeclarationAST) {
			result = interpret((VariableDeclarationAST) node);
		} else if (node instanceof VariableExpressionAST) {
			result = interpret((VariableExpressionAST) node);
		} else if (node instanceof WhileStatementAST) {
			result = interpret((WhileStatementAST) node);
		}
		return result;
	}

	private Object interpret(BinaryExpressionAST be) throws InterpreterException {
		List<AtsASTNode> children = be.getOutgoingNodes();
		// If the return type is 'String', we just call the toString method of each operand
		// and return the concatenation of these strings.
		if (be.getReturnType() == String.class) {
			String result = interpret(children.get(0)).toString();
			result = result.concat(interpret(children.get(1)).toString());
			return result;
		}
		Integer v1 = (Integer) interpret(children.get(0));
		Integer v2 = (Integer) interpret(children.get(1));
		
		switch(be.getOperator()) {
		case PLUS: return v1 + v2;
		case MINUS: return v1 - v2;
		case MULTIPLICATION: return v1 * v2;
		case DIVISION: return v1 / v2;
		default: throw new InterpreterException(be.getLocation(), " BinaryExpression: This type of operator is not supported: " + be.getOperator());
		}
	}
	
	private Object interpret(BreakStatementAST bst) {
		// Change the flow
		m_flow = Flow.BREAK;
		return null;
	}
	
	private Boolean interpret(ConditionalBooleanExpressionAST cbe) throws InterpreterException {
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
			String message = "ConditionalBooleanExpression: This type of operator is not supported: " + cbe.getOperator();
	    	throw new InterpreterException(cbe.getLocation(), message);  
	      }
		}
	}

	private Object interpret(ConstantExpressionAST ce) {
		return ce.getValue();
	}
	
	private Object interpret(ContinueStatementAST cst) {
		// Change the flow
		m_flow  =  Flow.CONTINUE;
		return null;
	}
	
	private Object interpret(ForStatementAST fs) throws InterpreterException {
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
	
	private Object interpret(IfElseStatementAST is) throws InterpreterException {
		List<AtsASTNode> children = is.getOutgoingNodes();
		
		// children(0) is the condition
		if ((Boolean) interpret(children.get(0))) {
			interpret(children.get(1));
		} else {
			interpret(children.get(2));
		}
		return null;
	}
	
	private Object interpret(IfStatementAST is) throws InterpreterException {
		List<AtsASTNode> children = is.getOutgoingNodes();
		if ((Boolean) interpret(children.get(0))) {
			for (int i = 1; i < children.size(); i++) {
				interpret(children.get(i));
			}
		}
		return null;
	}
	
	private NestedWord<String> interpret(NestedwordAST nw) {
		return new NestedWord<String>(nw.getWordSymbols(), nw.getNestingRelation());
	}
	
	private NestedLassoWord<String> interpret(NestedLassowordAST nw) {
		NestedWord<String> stem = interpret(nw.getStem());
		NestedWord<String> loop = interpret(nw.getLoop());
		return new NestedLassoWord<String>(stem, loop);
	}
	
	private Object interpret(OperationInvocationExpressionAST oe) throws InterpreterException {
		List<AtsASTNode> children = oe.getOutgoingNodes();
		if (children.size() != 1) {
			String message = "OperationExpression should have only 1 child (ArgumentList)";
			message = message.concat("Num of children: " + children.size());
			throw new InterpreterException(oe.getLocation(), message);
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
					m_ResultOfAssertStatements.add(new GenericResultAtElement<AtsASTNode>(oe, 
									Activator.s_PLUGIN_ID, 
							        UltimateServices.getInstance().getTranslatorSequence(),
							        "Assertion holds.", 
							        oe.getAsString(), 
							        Severity.INFO));
				} else {
					m_ResultOfAssertStatements.add(new GenericResultAtElement<AtsASTNode>(oe, 
									Activator.s_PLUGIN_ID, 
									UltimateServices.getInstance().getTranslatorSequence(),
									"Assertion violated!", 
									oe.getAsString(), 
									Severity.ERROR));
				}
			} else {
				throw new AssertionError("assert expects boolean result, type checker should have found this");
			}
		} else if (oe.getOperationName().equalsIgnoreCase("print")) {
			String argsAsString = children.get(0).getAsString();
			ILocation loc = children.get(0).getLocation();
			reportToLogger(LoggerSeverity.INFO, "Printing " + argsAsString);
			for (Object o : arguments) {
				final String text;
				if (o instanceof IAutomaton) {
					m_LastPrintedAutomaton = (IAutomaton<?, ?>) o;
					text = (new AtsDefinitionPrinter<String, String>("automaton", o)).getDefinitionAsString();
				} else {
					text = String.valueOf(o);
				}
				printMessage(Severity.INFO, LoggerSeverity.INFO, text, oe.getAsString(), oe);
				if (m_printAutomataToFile) {
					String comment = "/* " + oe.getAsString() + " */";
					m_printWriter.println(comment);
					m_printWriter.println(text);
				}

				
			}
			
		} else {
			IOperation<String,String> op = getAutomataOperation(oe, arguments);
			if (op != null) {
				try {
					assert op.checkResult(new StringFactory());
					result = op.getResult();
				} catch (AutomataLibraryException e) {
					throw new InterpreterException(oe.getLocation(),e.getMessage());
				} catch (OutOfMemoryError e) {
					throw new InterpreterException(oe.getLocation(), "OutOfMemoryError");
				}
			} 
		}
		return result;
	}
	
	private Boolean interpret(RelationalExpressionAST re) throws InterpreterException {
		List<AtsASTNode> children = re.getOutgoingNodes();
		if (re.getExpectingType() == Integer.class) {
			int v1 = (Integer) interpret(children.get(0));
			int v2 = (Integer) interpret(children.get(1));
			switch (re.getOperator()) {
			case GREATERTHAN: return v1 > v2;
			case LESSTHAN: return v1 < v2;
			case GREATER_EQ_THAN: return v1 >= v2;
			case LESS_EQ_THAN: return v1 <= v2;
			case EQ: return v1 == v2;
			case NOT_EQ: return v1 != v2;
			default: throw new InterpreterException(re.getLocation(), 
					"This type of operator is not supported: " + re.getOperator());
			}
		}
		return null;
	}
	
	private Object interpret(ReturnStatementAST rst) throws InterpreterException {
		List<AtsASTNode> children = rst.getOutgoingNodes();
		// Change the flow
		m_flow = Flow.RETURN;
		if (children.size() == 0) {
			return null;
		} else {
			return interpret(children.get(0));
		}
	}
	
	private Object interpret(StatementListAST stmtList) throws InterpreterException {
		for (AtsASTNode stmt : stmtList.getOutgoingNodes()) {
				interpret(stmt);
		}
		return null;
	}
	
    private Integer interpret(UnaryExpressionAST ue) throws InterpreterException {
		  List<AtsASTNode> children = ue.getOutgoingNodes();
		  
		  VariableExpressionAST var = (VariableExpressionAST) children.get(0);
		  Integer oldVal = (Integer) interpret(var);
	      
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
	    	throw new InterpreterException(ue.getLocation(), message);  
	      }
	      }
		}
	
    private Object interpret(VariableDeclarationAST vd) throws InterpreterException {
    	List<AtsASTNode> children = vd.getOutgoingNodes();
    	Object value = null;
    	if (children.size() == 1) {
    		value = interpret(children.get(0));
    	}
    	
    	for (String id : vd.getIdentifiers()) {
    		if (value == null) {
        		String longDescr = "Var \"" + id + "\" is assigned \"null\".";
    			throw new InterpreterException(vd.getLocation(), longDescr);    			
        	}
    		m_variables.put(id, value);
    	}
    	return null;
    }
    
	private Object interpret(VariableExpressionAST v) throws InterpreterException {
		if (!m_variables.containsKey(v.getIdentifier())) {
			String longDescr = "Variable \"" + v.getIdentifier() + "\" was not declared before.";
			throw new InterpreterException(v.getLocation(), longDescr);
		}
		return m_variables.get(v.getIdentifier());
	}
	
	private Object interpret(WhileStatementAST ws) throws InterpreterException {
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

	/**
	 * Reports the results of assert statements to the Logger and to Ultimate 
	 * as a GenericResult.
	 */
	private void reportResult(Finished finished) {
		s_Logger.info("----------------- Test Summary -----------------");
		boolean oneOrMoreAssertionsFailed = false;
		for (GenericResultAtElement<AtsASTNode> test : m_ResultOfAssertStatements) {
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, test);
			if (test.getSeverity() == Severity.ERROR) {
				oneOrMoreAssertionsFailed = true; 
			}
			reportToLogger(LoggerSeverity.INFO, "Line " + test.getLocation().getStartLine() + ": " + test.getShortDescription());
		}
		Severity userSeverity;
		final LoggerSeverity loggerSeverity;
		final String shortDescr;
		String longDescr;
		if (finished == Finished.FINISHED) {
			userSeverity = Severity.INFO;
			loggerSeverity = LoggerSeverity.INFO;
			shortDescr = "Finished interpretation of automata script.";
			longDescr = shortDescr;
			if (m_ResultOfAssertStatements.isEmpty()) {
				longDescr += " You have not used any assert statement in your automata" +
						" script. Assert statements can be used to check Boolean results.";
			} else if (!oneOrMoreAssertionsFailed) {
				longDescr += "All assert statements have been evaluated to true.";
			}
		} else if (finished == Finished.TIMEOUT) {
			userSeverity = Severity.WARNING;
			loggerSeverity = LoggerSeverity.INFO;
			shortDescr = "Timeout during interpretation of automata script.";
			longDescr = shortDescr;
		} else if (finished == Finished.OUTOFMEMORY) {
			userSeverity = Severity.WARNING;
			loggerSeverity = LoggerSeverity.INFO;
			shortDescr = "Run out of memory during interpretation of automata script.";
			longDescr = shortDescr;
		} else if (finished == Finished.ERROR) {
			userSeverity = Severity.ERROR;
			loggerSeverity = LoggerSeverity.ERROR;
			shortDescr = "Interpretation of automata script failed.";
			longDescr = shortDescr;
		} else {
			throw new AssertionError();
		}
		if (oneOrMoreAssertionsFailed) {
			userSeverity = Severity.ERROR;
			longDescr += "Some assert statements have been evaluated to false.";
		}
		printMessage(userSeverity, loggerSeverity, longDescr, shortDescr, null);
	}
	
	
	/**
	 * Reports the given string to the logger
	 * and to Ultimate as a GenericResult.
	 * @param sev the Severity
	 * @param longDescr the string to be reported
	 * @param node AtsASTNode for which this String is reported
	 */
	static void printMessage(Severity severityForResult, 
			LoggerSeverity severityForLogger, String longDescr, String shortDescr, AtsASTNode node) {
		reportToUltimate(severityForResult, longDescr, shortDescr, node);
		reportToLogger(severityForLogger, longDescr);
	}
	
	/**
	 * Reports the given string with the given severity to Ultimate as a GenericResult
	 * @param sev the severity
	 * @param longDescr the string to be reported
	 * @param node AtsASTNode for which this String is reported
	 */
	private static void reportToUltimate(Severity sev, String longDescr, String shortDescr, AtsASTNode node) {
			IResult result;
			if (node == null) {
				result = new GenericResult(
	                     Activator.s_PLUGIN_ID,
	                     shortDescr, longDescr, 
	                     sev);
			} else { 
				result = new GenericResultAtElement<AtsASTNode> (node,
					                     Activator.s_PLUGIN_ID, UltimateServices.getInstance().getTranslatorSequence(),
					                     shortDescr, longDescr, 
					                     sev);
			}
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, result);
	}
	
	/**
	 * Reports the given string with the given severity to the logger 
	 * @param sev the severity of the string
	 * @param toPrint the string to be printed
	 */
	private static void reportToLogger(LoggerSeverity sev, String toPrint) {
		switch (sev){
		case ERROR: s_Logger.error(toPrint); break;
		case INFO: s_Logger.info(toPrint); break;
		case WARNING: s_Logger.warn(toPrint); break;
		case DEBUG: s_Logger.debug(toPrint); break;
		default: s_Logger.info(toPrint); 
		}
	}

	/**
	 * Gets an object of an automata operation indicated by OperationInvocationExpression, if the operation exists
	 * and all arguments have correct type. Otherwise it returns null.
	 * @param oe the automata operation
	 * @param arguments the given arguments for this operation
	 * @return an object of the automata operation or null
	 * @throws InterpreterException if there couldn't construct an object of the operation
	 * @throws UnsupportedOperationException if the operation does not exist
	 */
	
	private IOperation<String,String> getAutomataOperation(OperationInvocationExpressionAST oe, ArrayList<Object> arguments) throws InterpreterException  {
		String operationName = oe.getOperationName().toLowerCase();
		IOperation<String,String> result = null;
		if (m_existingOperations.containsKey(operationName)) {
			Set<Class<?>> operationClasses = m_existingOperations.get(operationName);
			for (Class<?> operationClass : operationClasses) {
				Constructor<?>[] operationConstructors = operationClass.getConstructors();
				// Find the constructor which expects the correct arguments
				for (Constructor<?> c : operationConstructors) {
					if (allArgumentsHaveCorrectTypeForThisConstructor(c, arguments)) {
						try {
							result = (IOperation<String,String>) c.newInstance(arguments.toArray());
							return result;
						} catch (InstantiationException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (IllegalAccessException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (InvocationTargetException e) {
							Throwable targetException = e.getTargetException();
							if (targetException instanceof RuntimeException) {
								throw (RuntimeException) targetException;
							} else if (targetException instanceof InterpreterException) {
								throw (InterpreterException) targetException;
							} else if (targetException instanceof AutomataLibraryException) {
								throw new InterpreterException(oe.getLocation(), targetException.getMessage());
							} else if (targetException instanceof Error) {
								throw (Error) targetException;
							} else {
								String message = "Non runtime Exception" + targetException.getMessage();
								throw new AssertionError(message);
							}
						} catch (OutOfMemoryError e) {
							throw new InterpreterException(oe.getLocation(), "OutOfMemoryError");
						}
					}
				}					
			}
		} else {
			String allOperations = (new ListExistingOperations(m_existingOperations)).prettyPrint();
			String longDescr = "Unsupported operation \"" + operationName + "\"" + System.getProperty("line.separator") +
					"We support only the following operations " + System.getProperty("line.separator") + allOperations;
			throw new InterpreterException(oe.getLocation(), longDescr);
		}
		assert (result == null);
		{
			String shortDescr = "Operation error";
			String longDescr = "Operation \"" + oe.getOperationName() + "\" is not defined for " + 
			                   (arguments.size() == 1? "this type of argument." : "these types of arguments.");
			longDescr += " (";
			for (Object argument : arguments) {
				longDescr += argument.getClass().getSimpleName() + " ";
			}
			longDescr += ")";
			printMessage(Severity.ERROR, LoggerSeverity.DEBUG, longDescr, shortDescr, oe);
			throw new InterpreterException(oe.getLocation(), longDescr);
		}
	}
	
	
	/**
	 * Checks if all arguments have the correct type. 
	 * @param c The constructor of the operation class.
	 * @param arguments The arguments to check 
	 * @return true if and only if all arguments have the correct type. Otherwise false.
	 */
	private boolean allArgumentsHaveCorrectTypeForThisConstructor(Constructor<?> c, List<Object> arguments) {
		if (arguments.size() != c.getParameterTypes().length) return false;
		int i = 0;
		int minArgSize = (c.getParameterTypes().length > arguments.size() ? arguments.size() : c.getParameterTypes().length);
		for (Class<?> type : c.getParameterTypes()) {
			if ((i >= minArgSize) || !(AssignableTest.isAssignableFrom(type, arguments.get(i).getClass()))) {
				return false;
			}
			++i;
		}
		return true;
	}
	

	/**
	 * Finds all automata operations implementing the IOperation interface. It maps the operation names
	 * to set of class objects, because there may exist different classes for the same operation.
	 * E.g. accepts-operation for NestedWordAutomata and accepts-operations for PetriNets
	 * @return A map from class names to set of class objects from classes found in the directories.
 	 */
	private static Map<String, Set<Class<?>>> getOperationClasses() {
		Map<String, Set<Class<?>>> result = new HashMap<String, Set<Class<?>>>();
		String[] baseDirs = {"/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/operations",
							"/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/operationsOldApi",
							"/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/operations/minimization",
				              "/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/buchiNwa",
				              "/de/uni_freiburg/informatik/ultimate/automata/petrinet/julian",
				              "/de/uni_freiburg/informatik/ultimate/automata/petrinet"};
		for (String baseDir : baseDirs) {
			ArrayDeque<String> dirs = new ArrayDeque<String>();
			dirs.add("");
			while (!dirs.isEmpty()) {
				String dir = dirs.removeFirst();
				String[] files = filesInDirectory(baseDir + "/" + dir);
				for (String file : files) {
					if (file.endsWith(".class")) {
						String fileWithoutSuffix = file.substring(0, file.length()-6);
						String baseDirInPackageFormat = baseDir.replaceAll("/", ".");
						if (baseDirInPackageFormat.charAt(0) == '.') {
							baseDirInPackageFormat = baseDirInPackageFormat.substring(1);
						}
						String path = "";
						if (dir.isEmpty()) {
							path = baseDirInPackageFormat + "." + fileWithoutSuffix;
						} else {
							path = baseDirInPackageFormat + "." + dir + "." + fileWithoutSuffix;
						}
						Class<?> clazz = null;
						try {
							clazz = Class.forName(path);
						} catch (ClassNotFoundException e) {
							e.printStackTrace();
							s_Logger.error("Couldn't load/find class " + path);
							break;
						}
						if ((clazz != null) && (classImplementsIOperationInterface(clazz))) {
							String operationName = fileWithoutSuffix.toLowerCase();
							if (result.containsKey(operationName)) {
								Set<Class<?>> s = result.get(operationName);
								s.add(clazz);
							} else {
								Set<Class<?>> s = new HashSet<Class<?>>();
								s.add(clazz);
								result.put(operationName, s);
							}
							
							
						}
					}
					// if the file has no ending, it may be a directory
					else if (!file.contains(".")) {
						try {
							if (isDirectory(baseDir + "/" + file)) {
								dirs.addLast(file);
							}
						} catch (Exception e) {
							
						}
					}
				}
			}
		}
		return result;
	}
	
	
	/**
	 * Checks if the given class object implements the IOperation interface.
	 * @param c the class object to check
	 * @return true if and only if the class object c implements the IOperation interface. Otherwise false.
	 */
	private static boolean classImplementsIOperationInterface(Class<?> c) {
		Class<?>[] implementedInterfaces = c.getInterfaces();
		for (Class<?> interFace : implementedInterfaces) {
			if (interFace.equals(IOperation.class)) {
				return true;
			}
		}
		return false;
	}
	
	private static boolean isDirectory(String dir) {
		URL dirURL = IOperation.class.getClassLoader().getResource(dir);
		if (dirURL == null) return false;
		else return dirURL.getProtocol().equals("bundleresource");
	}
	
	/**
	 * Return the filenames of the files in the given
	 * directory.
	 * We use the classloader to get the URL of this folder. We support only
	 * URLs with protocol <i>file</i> and <i>bundleresource</i>.
	 * At the moment these are the only ones that occur in Website and
	 * WebsiteEclipseBridge.
	 */
	private static String[] filesInDirectory(String dir) {
		URL dirURL = IOperation.class.getClassLoader().getResource(dir);
		if (dirURL == null) {
			// throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
			s_Logger.error("Directory \"" + dir + "\" does not exist");
			return new String[0];
		}
		String protocol = dirURL.getProtocol();
		File dirFile = null;
		if (protocol.equals("file")) {
			try {
				dirFile = new File(dirURL.toURI());
			} catch (URISyntaxException e) {
				e.printStackTrace();
				// throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
				s_Logger.error("Directory \"" + dir + "\" does not exist");
				return new String[0];
			}
		} else if (protocol.equals("bundleresource")) {
			try {
				URL fileURL = FileLocator.toFileURL(dirURL);
				dirFile = new File(fileURL.toURI());
			} catch (Exception e) {
				e.printStackTrace();
				// throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
				s_Logger.error("Directory \"" + dir + "\" does not exist");
				return new String[0];
			}
		} else {
			throw new UnsupportedOperationException("unknown protocol");
		}
		String[] files = dirFile.list();
		return files;
	}
	
	
	/**
	 * Exception that is thrown if the interpreter has found an error in the
	 * ats file. m_ShortDescription may be null which means that no 
	 * shortDescription is provided.
	 *
	 */
	private class InterpreterException extends Exception {
		private static final long serialVersionUID = -7514869048479460179L;
		private final ILocation m_Location;
		private final String m_ShortDescription;
		private final String m_LongDescription;
		public InterpreterException(ILocation m_Location,
				String longDescription) {
			super();
			this.m_Location = m_Location;
			this.m_LongDescription = longDescription;
			this.m_ShortDescription = null;
		}
		public InterpreterException(ILocation m_Location,
				String longDescription,
				String shortDescription) {
			super();
			this.m_Location = m_Location;
			this.m_LongDescription = longDescription;
			this.m_ShortDescription = shortDescription;
		}
		public ILocation getLocation() {
			return m_Location;
		}
		public String getLongDescription() {
			return m_LongDescription;
		}
		public String getShortDescription() {
			return m_ShortDescription;
		}
		
	}
	
}
