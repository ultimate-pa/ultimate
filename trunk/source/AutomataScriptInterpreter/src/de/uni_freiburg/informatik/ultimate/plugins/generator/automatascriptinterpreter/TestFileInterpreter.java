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
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.preferences.PreferenceConstants;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.ILocation;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AutomataScriptLocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AssignmentExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFile;
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
	
	private static String UNKNOWN_OPERATION = "UNKNOWN_OPERATION";
	
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
		 * Location of the current AtsAST node. It is helpful to locate the place, where
		 * the error happened.
		 */
		private ILocation m_errorLocation = null;
		private String m_shortDescription = "Typecheck error";
		private String m_longDescription = "";
		
		/**
		 * Checks the test file for type errors and for
		 * undeclared variables.
		 * @param n the root node of the AST 
		 * @throws IllegalArgumentException
		 */
		public void checkTestFile(AtsASTNode n) throws IllegalArgumentException {
			for (Map.Entry<String, Object > entry : m_variables.entrySet()) {
				m_localVariables.put(entry.getKey(), entry.getValue().getClass());
			}
			checkType(n);
		}
		
		private void checkType(AtsASTNode n) throws IllegalArgumentException {
			if (n instanceof AssignmentExpression) {
				checkType((AssignmentExpression) n);
			} else if (n instanceof BinaryExpression) {
				checkType((BinaryExpression) n);
			}  else if (n instanceof ConditionalBooleanExpression) {
				checkType((ConditionalBooleanExpression) n);
			} else if (n instanceof ForStatement) {
				checkType((ForStatement) n);
			} else if (n instanceof IfElseStatement) {
				checkType((IfElseStatement) n);
			} else if (n instanceof IfStatement) {
				checkType((IfStatement) n);
			} else if (n instanceof OperationInvocationExpression) {
				checkType((OperationInvocationExpression) n);
			} else if (n instanceof RelationalExpression) {
				checkType((RelationalExpression) n);
			} else if (n instanceof StatementList) {
				for (AtsASTNode stmt : ((StatementList)n).getOutgoingNodes()) {
					checkType(stmt);
				}
			} else if (n instanceof UnaryExpression) {
				checkType((UnaryExpression) n);
			} else if (n instanceof VariableDeclaration) {
				checkType((VariableDeclaration) n);
			} else if (n instanceof VariableExpression) {
				checkType((VariableExpression) n);
			} else if (n instanceof WhileStatement) {
				checkType((WhileStatement) n);
			}
				
		}
		
		private void checkType(AssignmentExpression as) throws IllegalArgumentException {
			List<AtsASTNode> children = as.getOutgoingNodes();
			m_errorLocation = as.getLocation();
			if (children.size() != 2) {
				m_shortDescription = "Error";
				String message = "Assignment should have 2 operands." + System.getProperty("line.separator");
				message = message.concat("On the left-hand side there  must be a variable, ");
				message = message.concat("on the right-hand side there can be an arbitrary expression.");
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// Check the type of children
			checkType(children.get(0));
			checkType(children.get(1));
			
			VariableExpression var = (VariableExpression) children.get(0);
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
			m_longDescription = message;
			throw new IllegalArgumentException(message);
			
		}
		
		private void checkType(BinaryExpression be)  throws IllegalArgumentException {
			List<AtsASTNode> children = be.getOutgoingNodes();
			m_errorLocation = be.getLocation();
			if (children.size() != 2) {
				m_shortDescription  = "Error";
				String message = be.getOperatorAsString() + " should have 2 operands of type \"int\"." +
				                 System.getProperty("line.separator") + "Num of operands: " + children.size();
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// Check children for correct type
			checkType(children.get(0));
			checkType(children.get(1));
			
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
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			
			// Check whether second child has expected type.
			for (Class<?> c : getTypes(children.get(1))) {
				if (AssignableTest.isAssignableFrom(be.getReturnType(), c)) {
					return;
				}
			}
			String message = "Right operand of \"" + be.getOperatorAsString() + "\" has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + be.getReturnType().getSimpleName() + "\tGot: " + children.get(1).getReturnType().getSimpleName() + "");
			m_longDescription = message;
			throw new IllegalArgumentException(message);

		}
		
		private void checkType(ConditionalBooleanExpression cbe)  throws IllegalArgumentException {
			List<AtsASTNode> children = cbe.getOutgoingNodes();
			m_errorLocation = cbe.getLocation();
			if ((cbe.getOperator() == ConditionalBooleanOperator.NOT) && (children.size() != 1)) {
				m_shortDescription = "Error";
				String message = "\"!\" operator should have 1 operand." + System.getProperty("line.separator") + "Num of operands: " + children.size();
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			} else if ((cbe.getOperator() == ConditionalBooleanOperator.AND) && (children.size() != 2)) {
				m_shortDescription = "Error";
				String message = "\"&&\" operator should have 2 operands." + System.getProperty("line.separator") + "Num of operands: " + children.size();
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			} else if ((cbe.getOperator() == ConditionalBooleanOperator.OR) && (children.size() != 2)) {
				m_shortDescription = "Error";
				String message = " \"||\" operator should have 2 operands." + System.getProperty("line.separator") + "Num of operands: " + children.size();
				m_longDescription = message;
				throw new IllegalArgumentException(message);
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
				m_longDescription = message;
				throw new IllegalArgumentException(message);
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
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(ForStatement fs)  throws IllegalArgumentException {
			List<AtsASTNode> children = fs.getOutgoingNodes();
			m_errorLocation = fs.getLocation();
			if (children.size() != 4) {
				m_shortDescription = "Error";
				String message = "ForStatement should have 4 arguments (initStmt, condition, updateStmt) {stmtList}." + System.getProperty("line.separator");
				message = message.concat("Num of children: " + children.size());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// First child is the loop condition.
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = "Loopcondition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(IfElseStatement is)  throws IllegalArgumentException {
			List<AtsASTNode> children = is.getOutgoingNodes();
			m_errorLocation = is.getLocation();
			if (children.size() != 3) {
				m_shortDescription = "Error";
				String message = "IfElseStatement should have 3 operands (Condition) { Thenstatements} {Elsestatements})" + System.getProperty("line.separator");
				message = message.concat("Num of operands: " + children.size());
				throw new IllegalArgumentException(message);
			}
			// Check the children for correct type.
			checkType(children.get(0));
			// Check if the if-condition has type Boolean.
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(IfStatement is)  throws IllegalArgumentException {
			List<AtsASTNode> children = is.getOutgoingNodes();
			m_errorLocation = is.getLocation();
			if (children.size() != 2) {
				m_shortDescription = "Error";
				String message = "IfStatement should have 2 operands (condition) {thenStatements}" +System.getProperty("line.separator");
				message = message.concat("Num of operands: " + children.size());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// Check the first child for correct type
			checkType(children.get(0));
			// Check if the if-condition has type Boolean.
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(OperationInvocationExpression oe) throws IllegalArgumentException {
			m_errorLocation = oe.getLocation();
			String opName = oe.getOperationName().toLowerCase();
			if (!m_existingOperations.containsKey(opName)) {
				if (!opName.equals("assert") && !opName.equals("print")) {
					String shortDescr = "Unsupported operation \"" + oe.getOperationName() + "\"";
					m_shortDescription = shortDescr;
					String allOperations = (new ListExistingOperations(m_existingOperations)).prettyPrint();
					String longDescr = "We support only the following operations " + System.getProperty("line.separator") + allOperations;
					m_longDescription = longDescr;
					throw new UnsupportedOperationException(shortDescr);
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
		
		private void checkType(RelationalExpression re)  throws IllegalArgumentException {
			List<AtsASTNode> children = re.getOutgoingNodes();
			m_errorLocation = re.getLocation();
			if (children.size() != 2) {
				m_shortDescription = "Error";
				String message = "\"" + re.getOperatorAsString() + " should have 2 operands." + System.getProperty("line.separator") + "Num of operands: "
				                 + children.size();
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// Check children for correct type
			checkType(children.get(0));
			checkType(children.get(1));
			// Check whether first child has expected type.
			boolean firstChildHasCorrectType = false;
			for (Class<?> c : getTypes(children.get(0))) {
				if (c.isAssignableFrom(re.getExpectingType())) {
					firstChildHasCorrectType = true;
				}
			}
			if (!firstChildHasCorrectType) {
				String message = "Left operand has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + re.getExpectingType().getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// Check whether second child has expected type.
			for (Class<?> c : getTypes(children.get(1))) {
				if (c.isAssignableFrom(re.getExpectingType())) {
					return;
				}
			}
			String message = "Right operand has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + re.getExpectingType().getSimpleName() + "\tGot: " + children.get(1).getReturnType().getSimpleName());
			m_longDescription = message;
			throw new IllegalArgumentException(message);
		}
		
		private void checkType(UnaryExpression ue)  throws IllegalArgumentException {
			List<AtsASTNode> children = ue.getOutgoingNodes();
			m_errorLocation = ue.getLocation();
			if (children.size() != 1) {
				m_shortDescription = "Error";
				String message = "\"" + ue.getOperatorAsString() + "\" should have one variable as argument." + System.getProperty("line.separator") + "Num of arguments: " + children.size();
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// Check children for correct type
			checkType(children.get(0));
			
			if (!(children.get(0) instanceof VariableExpression)) {
				m_shortDescription = "Error";
				String message = "Unary operators are applicable only on variables." + System.getProperty("line.separator") + "You want to apply it on " + children.get(0).getClass().getSimpleName();
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			// Check if variable has expected type, namely
			// type 'int'
			for (Class<?> c : getTypes(children.get(0))) {
				if (c.isAssignableFrom(ue.getReturnType())) {
					return;
				}
			}
			String message = "Operand has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + ue.getExpectingType().getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
			m_longDescription = message;
			throw new IllegalArgumentException(message);
		}
		
		private void checkType(VariableExpression v) {
			m_errorLocation = v.getLocation();
			if (m_localVariables.containsKey(v.getIdentifier())) {
				v.setType(m_localVariables.get(v.getIdentifier()));
			} else {
				m_shortDescription = "Undeclared variable";
				String message = "Variable \"" + v.getIdentifier() + "\" at line " + v.getLocation().getStartLine() + " was not declared.";
				m_longDescription = "Variable \"" + v.getIdentifier() + "\" was not declared.";
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(VariableDeclaration vd)  throws IllegalArgumentException {
			List<AtsASTNode> children = vd.getOutgoingNodes();
			m_errorLocation = vd.getLocation();
	    	if ((children.size() != 0) && (children.size() != 1)) {
	    		m_shortDescription = "Error";
	    		String message = "Variabledeclaration can have at most one operand. (the value to assign)";
	    		m_longDescription = message;
				throw new IllegalArgumentException(message);
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
	    	m_longDescription = message;
	    	throw new IllegalArgumentException(message);
		}
		
		private void checkType(WhileStatement ws)  throws IllegalArgumentException {
			List<AtsASTNode> children = ws.getOutgoingNodes();
			m_errorLocation = ws.getLocation();
			if (children.size() != 2) {
				m_shortDescription = "Error";
				String message = "WhileStatement should have 2 operands (condition) {stmtList}" + System.getProperty("line.separator");
				message = message.concat("Number of children: " + children.size());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
			}
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: " + children.get(0).getReturnType().getSimpleName());
				m_longDescription = message;
				throw new IllegalArgumentException(message);
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
			if (n instanceof OperationInvocationExpression) {
				OperationInvocationExpression oe = (OperationInvocationExpression) n;
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

		
		public ILocation getErrorLocation() {
			return m_errorLocation;
		}

		public String getShortDescription() {
			return m_shortDescription;
		}

		public String getLongDescription() {
			return m_longDescription;
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
	 * Contains the test cases defined in the current automatascript test file.
	 * Each assert-operation forms a test case.
	 */
	private List<GenericResult<Integer>> m_testCases;
	/**
	 * The automaton, which was lastly printed by a print operation. 
	 */
	private IAutomaton<?, ?> m_LastPrintedAutomaton;
	/**
	 * 
	 */
	private int m_timeout = 60;
	/**
	 * Indicates whether the automaton, which is output by a print operation, should
	 * also be printed to a .ats-file.
	 */
	private boolean m_printAutomataToFile = false;
	private PrintWriter m_printWriter;
	private String m_path = ".";
	private ILocation m_errorLocation;
	public enum LoggerSeverity {INFO, WARNING, ERROR, DEBUG};
	/**
	 * If an error occurred during the interpretation this is set to true
	 * and further interpretation is aborted.
	 */
	private boolean m_ErrorOccured = false;
	
	
	public TestFileInterpreter() {
		readPreferences();
		m_variables = new HashMap<String, Object>();
		m_flow = Flow.NORMAL;
		m_automInterpreter = new AutomataDefinitionInterpreter();
		m_testCases = new ArrayList<GenericResult<Integer>>();
		m_tChecker = new AutomataScriptTypeChecker();
		m_existingOperations = getOperationClasses();
		m_LastPrintedAutomaton = null;
		m_errorLocation = getPseudoLocation();
		AssignableTest.initPrimitiveTypes();
		UltimateServices.getInstance().setDeadline(System.currentTimeMillis() + (m_timeout * 1000));
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
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.s_PLUGIN_ID);
		m_timeout = prefs.getInt(PreferenceConstants.Name_Timeout, 
				PreferenceConstants.Default_Timeout);
		m_printAutomataToFile = prefs.getBoolean(PreferenceConstants.Name_WriteToFile, 
				PreferenceConstants.Default_WriteToFile);
		m_path = prefs.get(PreferenceConstants.Name_Path, 
				PreferenceConstants.Default_Path);
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
		AutomataTestFile ats = null;
		if (node instanceof AutomataTestFile) {
			ats = (AutomataTestFile) node;
		}
		reportToLogger(LoggerSeverity.DEBUG, "Interpreting automata definitions...");
		// Interpret automata definitions
		try {
			m_automInterpreter.interpret(ats.getAutomataDefinitions());
		} catch (Exception e) {
			reportToLogger(LoggerSeverity.INFO, "Error during interpreting automata definitions.");
			reportToLogger(LoggerSeverity.INFO, "Error: " + e.getMessage());
			reportToLogger(LoggerSeverity.INFO, "Interpretation of testfile cancelled.");
			reportToUltimate(Severity.ERROR, e.getMessage() + " Interpretation of testfile cancelled.", "Error", m_automInterpreter.getErrorLocation());
		}
		

		// Put all defined automata into variables map
		m_variables.putAll(m_automInterpreter.getAutomata());
		reportToLogger(LoggerSeverity.DEBUG, "Typechecking of test file...");
		// Type checking
		try {
			m_tChecker.checkTestFile(ats.getStatementList());
		} catch (Exception e) {
			reportToLogger(LoggerSeverity.INFO, "Error: " + e.getMessage());
			reportToLogger(LoggerSeverity.INFO, "Interpretation of testfile cancelled.");
			reportToUltimate(Severity.ERROR, m_tChecker.getLongDescription(), m_tChecker.getShortDescription(), m_tChecker.getErrorLocation());
			return null;
		}
		
		
		// Interpreting test file
		Object result = null;
		reportToLogger(LoggerSeverity.DEBUG, "Interpreting test file...");
		if (ats.getStatementList() == null) {
			// File contains only automata definitions no testcases.
			result = null;
		} else {
			try {
				result = interpret(ats.getStatementList());
			} catch (Exception e) {
				reportToLogger(LoggerSeverity.DEBUG, e.getMessage());
				reportToUltimate(Severity.ERROR, e.getMessage(), "Error", m_errorLocation);
				return null;
			}
		}
		reportToLogger(LoggerSeverity.DEBUG, "Reporting results...");
		reportResult();
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
	
	private <T> Object interpret(AssignmentExpression as) throws NoSuchFieldException {
		List<AtsASTNode> children = as.getOutgoingNodes();
		VariableExpression var = (VariableExpression) children.get(0);
		if (!m_variables.containsKey(var.getIdentifier())) {
			String message = as.getLocation().getStartLine() + ": Variable \"" + var.getIdentifier() + "\" was not declared before.";
			throw new NoSuchFieldException(message);
		}
		Object oldValue = m_variables.get(var.getIdentifier());
		Object newValue = interpret(children.get(1));
		
		if (newValue == null) {
			String longDescr = "Var \"" + var.getIdentifier() + "\" is assigned \"null\".";
			String shortDescr = "Null assignment";
			printMessage(Severity.WARNING, LoggerSeverity.DEBUG, longDescr, shortDescr, as.getLocation());
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
			throw new UnsupportedOperationException("AssignmentExpression: This type of operator is not supported: " + as.getOperator());
		}
			
		}
		
		return oldValue;
	}
		
	private <T> Object interpret(AtsASTNode node) throws NoSuchFieldException {
		m_errorLocation = node.getLocation();
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
			try {
				result = interpret((OperationInvocationExpression) node);
			} catch (Exception e) {
				throw new RuntimeException(e.getMessage());
			}
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

	private <T> Integer interpret(BinaryExpression be) throws NoSuchFieldException {
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
	
	private <T> Object interpret(BreakStatement bst) {
		// Change the flow
		m_flow = Flow.BREAK;
		return null;
	}
	
	private <T> Boolean interpret(ConditionalBooleanExpression cbe) throws NoSuchFieldException {
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
	
	private <T> Object interpret(ContinueStatement cst) {
		// Change the flow
		m_flow  =  Flow.CONTINUE;
		return null;
	}
	
	private <T> Object interpret(ForStatement fs) throws NoSuchFieldException {
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
	
	private <T> Object interpret(IfElseStatement is) throws NoSuchFieldException {
		List<AtsASTNode> children = is.getOutgoingNodes();
		
		// children(0) is the condition
		if ((Boolean) interpret(children.get(0))) {
			interpret(children.get(1));
		} else {
			interpret(children.get(2));
		}
		return null;
	}
	
	private <T> Object interpret(IfStatement is) throws NoSuchFieldException {
		List<AtsASTNode> children = is.getOutgoingNodes();
		if ((Boolean) interpret(children.get(0))) {
			for (int i = 1; i < children.size(); i++) {
				interpret(children.get(i));
			}
		}
		return null;
	}
	
	private <T> NestedWord<String> interpret(Nestedword nw) {
		return new NestedWord<String>(nw.getWordSymbols(), nw.getNestingRelation());
	}
	
	private <T> NestedLassoWord<String> interpret(NestedLassoword nw) {
		NestedWord<String> stem = interpret(nw.getStem());
		NestedWord<String> loop = interpret(nw.getLoop());
		return new NestedLassoWord<String>(stem, loop);
	}
	
	private <T> Object interpret(OperationInvocationExpression oe) throws Exception {
		List<AtsASTNode> children = oe.getOutgoingNodes();
		if (children.size() != 1) {
			String message ="Line "  + oe.getLocation().getStartLine() + ": OperationExpression should have only 1 child (ArgumentList)";
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
							        oe.getAsString(), 
							        Severity.INFO));
				} else {
					m_testCases.add(new GenericResult<Integer>(oe.getLocation().getStartLine(), 
									Activator.s_PLUGIN_ID, 
									null,
									oe.getLocation(), 
									"Assertion violated!", 
									oe.getAsString(), 
									Severity.ERROR));
				}
			}
		} else if (oe.getOperationName().equalsIgnoreCase("print")) {
			String argsAsString = children.get(0).getAsString();
			ILocation loc = children.get(0).getLocation();
			reportToLogger(LoggerSeverity.INFO, "Printing " + argsAsString);
			for (Object o : arguments) {
				if (o instanceof IAutomaton) {
					m_LastPrintedAutomaton = (IAutomaton<?, ?>) o;
					String automatonAsString = (new AtsDefinitionPrinter(o)).getDefinitionAsString();
					printMessage(Severity.INFO, LoggerSeverity.INFO, automatonAsString, oe.getAsString(), loc);
					if (m_printAutomataToFile) {
						String comment = "/* " + oe.getAsString() + " */";
						m_printWriter.println(comment);
						m_printWriter.println(automatonAsString);
					}
					
				} else {
					printMessage(Severity.INFO, LoggerSeverity.INFO, o.toString(), oe.getAsString(), loc);
					if (m_printAutomataToFile) {
						String comment = "/* " + oe.getAsString() + " */";
						m_printWriter.println(comment);
						m_printWriter.println(o.toString());
					}
				}
				
			}
			
		} else {
			IOperation op = getAutomataOperation(oe, arguments);
			if (op != null) {
				result = op.getResult();
			} 
		}
		return result;
	}
	
	private <T> Boolean interpret(RelationalExpression re) throws NoSuchFieldException {
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
			default: throw new UnsupportedOperationException("This type of operator is not supported: " + re.getOperator());
			}
		}
		return null;
	}
	
	private <T> Object interpret(ReturnStatement rst) throws NoSuchFieldException {
		List<AtsASTNode> children = rst.getOutgoingNodes();
		// Change the flow
		m_flow = Flow.RETURN;
		if (children.size() == 0) {
			return null;
		} else {
			return interpret(children.get(0));
		}
	}
	
	private <T> Object interpret(StatementList stmtList) {
		for (AtsASTNode stmt : stmtList.getOutgoingNodes()) {
			if (m_ErrorOccured) {
				return null;
			}
			try {
				interpret(stmt);
			} catch (Exception e) {
				m_ErrorOccured = true;
				if (e.getMessage() != null && e.getMessage().equals(UNKNOWN_OPERATION)) {
					// do nothing - result was already reported
				} else {
					TestFileInterpreter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.toString() 
							+ System.getProperty("line.separator") + e.getStackTrace(), 
							"Exception thrown.", stmt.getLocation());
					return null;
				}
			}
		}
		return null;
	}
	
    private <T> Integer interpret(UnaryExpression ue) {
		  List<AtsASTNode> children = ue.getOutgoingNodes();
		  
		  VariableExpression var = (VariableExpression) children.get(0);
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
	    	throw new UnsupportedOperationException(message);  
	      }
	      }
		}
	
    private <T> Object interpret(VariableDeclaration vd) throws NoSuchFieldException {
    	List<AtsASTNode> children = vd.getOutgoingNodes();
    	Object value = null;
    	if (children.size() == 1) {
    		value = interpret(children.get(0));
    	}
    	
    	for (String id : vd.getIdentifiers()) {
    		if (value == null) {
        		String longDescr = "Var \"" + id + "\" is assigned \"null\".";
    			String shortDescr = "Null assignment";
    			printMessage(Severity.WARNING, LoggerSeverity.DEBUG, longDescr, shortDescr, vd.getLocation());
        	}
    		m_variables.put(id, value);
    	}
    	return null;
    }
    
	private <T> Object interpret(VariableExpression v) {
		if (!m_variables.containsKey(v.getIdentifier())) {
			throw new IllegalArgumentException("Variable \"" + v.getIdentifier() + "\" was not declared before.");
		}
		return m_variables.get(v.getIdentifier());
	}
	
	private <T> Object interpret(WhileStatement ws) throws NoSuchFieldException {
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
	private void reportResult() {
		s_Logger.info("----------------- Test Summary -----------------");
		if (m_ErrorOccured) {
			printMessage(Severity.ERROR, LoggerSeverity.INFO, 
					" ERROR: Interpretation of automata script file was aborted", 
					"Unable to interpret automata script file", getPseudoLocation());
		} else {
			String testCasesSummary = "All testcases passed.";
			for (GenericResult<Integer> test : m_testCases) {
				UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, test);
				if (test.getSeverity() == Severity.ERROR) testCasesSummary = "Some testcases failed.";
				reportToLogger(LoggerSeverity.INFO, "Line " + test.getLocation().getStartLine() + ": " + test.getShortDescription());
			}
			// Report summary of the testcases/
			if (m_testCases.isEmpty()) {
				printMessage(Severity.WARNING, LoggerSeverity.INFO, "No testcases defined!", "Warning" ,  getPseudoLocation());
			} else {
			reportToLogger(LoggerSeverity.INFO, testCasesSummary);
			}
		}
	}
	
	
	/**
	 * Reports the given string to the logger
	 * and to Ultimate as a GenericResult.
	 * @param sev the Severity
	 * @param longDescr the string to be reported
	 * @param loc the location of the String
	 */
	static void printMessage(Severity severityForResult, LoggerSeverity severityForLogger, String longDescr, String shortDescr, ILocation loc) {
		reportToUltimate(severityForResult, longDescr, shortDescr, loc);
		reportToLogger(severityForLogger, longDescr);
	}
	
	/**
	 * Reports the given string with the given severity to Ultimate as a GenericResult
	 * @param sev the severity
	 * @param longDescr the string to be reported
	 * @param loc the location of the string
	 */
	private static void reportToUltimate(Severity sev, String longDescr, String shortDescr, ILocation loc) {
			GenericResult<Integer> res = new GenericResult<Integer> ((loc != null ? loc.getStartLine() : 0),
					                     Activator.s_PLUGIN_ID, null,
					                     loc,
					                     shortDescr, longDescr, 
					                     sev);
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
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
	 * @throws Exception if there couldn't construct an object of the operation
	 * @throws UnsupportedOperationException if the operation does not exist
	 */
	private IOperation getAutomataOperation(OperationInvocationExpression oe, ArrayList<Object> arguments) throws Exception  {
		String operationName = oe.getOperationName().toLowerCase();
		IOperation result = null;
		if (m_existingOperations.containsKey(operationName)) {
			Set<Class<?>> operationClasses = m_existingOperations.get(operationName);
			for (Class<?> operationClass : operationClasses) {
				Constructor<?>[] operationConstructors = operationClass.getConstructors();
				// Find the constructor which expects the correct arguments
				for (Constructor<?> c : operationConstructors) {
					if (allArgumentsHaveCorrectTypeForThisConstructor(c, arguments)) {
						try {
							result = (IOperation) c.newInstance(arguments.toArray());
							return result;
						} catch (InstantiationException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (IllegalAccessException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (IllegalArgumentException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (InvocationTargetException e) {
							throw (Exception) e.getCause();
						}
					}
				}					
			}
		} else {
			String shortDescr = "Unsupported operation \"" + operationName + "\"";
			String allOperations = (new ListExistingOperations(m_existingOperations)).prettyPrint();
			String longDescr = "We support only the following operations " + System.getProperty("line.separator") + allOperations;
			reportToUltimate(Severity.ERROR, longDescr, shortDescr, oe.getLocation());
			reportToLogger(LoggerSeverity.DEBUG, shortDescr);
			throw new UnsupportedOperationException(UNKNOWN_OPERATION);
		}
		if (result == null) {
			String shortDescr = "Operation error";
			String longDescr = "Operation \"" + oe.getOperationName() + "\" is not defined for " + 
			                   (arguments.size() == 1? "this type of argument." : "these types of arguments.");
			longDescr += " (";
			for (Object argument : arguments) {
				longDescr += argument.getClass().getSimpleName() + " ";
			}
			longDescr += ")";
			printMessage(Severity.ERROR, LoggerSeverity.DEBUG, longDescr, shortDescr, oe.getLocation());
		}
		return result;
	}
	
	
	/**
	 * Checks if all arguments have the correct type. 
	 * @param c The constructor of the operation class.
	 * @param arguments The arguments to check 
	 * @return true if and only if all arguments have the correct type. Otherwise false.
	 */
	private boolean allArgumentsHaveCorrectTypeForThisConstructor(Constructor<?> c, List<Object> arguments) {
		if (arguments == null && c.getParameterTypes().length != 0) return false;
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
	 * Finds all automata operations implementing the IOperation interface. It maps the operation names
	 * to set of class objects, because there may exist different classes for the same operation.
	 * E.g. accepts-operation for NestedWordAutomata and accepts-operations for PetriNets
	 * @return A map from class names to set of class objects from classes found in the directories.
 	 */
	private static Map<String, Set<Class<?>>> getOperationClasses() {
		Map<String, Set<Class<?>>> result = new HashMap<String, Set<Class<?>>>();
		String[] baseDirs = {"/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/operations",
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
	
	private static ILocation getPseudoLocation() {
		return new AutomataScriptLocation("", 0, 0, 0, 0);
	}
	
}
