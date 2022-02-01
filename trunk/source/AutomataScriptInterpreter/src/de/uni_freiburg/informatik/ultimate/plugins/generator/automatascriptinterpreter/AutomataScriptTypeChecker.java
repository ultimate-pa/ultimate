/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptInterpreter plug-in.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptInterpreter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptInterpreter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptInterpreter plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AssignmentExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BinaryExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanOperatorAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ForStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfElseStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.OperationInvocationExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.RelationalExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.StatementListAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.UnaryExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableDeclarationAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.WhileStatementAST;

/**
 * This class implements a static type checker for the automatascript files.
 * 
 * @author musab@informatik.uni-freiburg.de
 */
class AutomataScriptTypeChecker {
	private static final int NUMBER_OF_FOR_ARGUMENTS = 4;
	private static final int NUMBER_OF_ITE_ARGUMENTS = 3;
	
	private static final String GOT = "\tGot: ";
	private static final String CONDITION_HAS_INCORRECT_TYPE = "Condition has incorrect type.";
	private static final String NUM_OF_OPERANDS = "Num of operands: ";
	private static final String EXPECTED = "Expected: ";
	private static final String LINE_SEPARATOR = System.getProperty("line.separator");
	
	private final Map<String, Set<Class<?>>> mExistingOperations;
	
	/**
	 * A map from variable names to the type they represent. This is needed to check for type conformity, e.g.
	 * variable assignment.
	 */
	private final Map<String, Class<?>> mLocalVariables = new HashMap<>();
	
	AutomataScriptTypeChecker(final Map<String, Set<Class<?>>> existingOperations) {
		mExistingOperations = existingOperations;
	}
	
	/**
	 * Checks the test file for type errors and for undeclared variables.
	 * 
	 * @param n
	 *            the root node of the AST
	 * @param variables
	 *            global variables (a local copy is made that can be edited)
	 */
	public void checkTestFile(final AtsASTNode n, final Map<String, Object> variables) throws InterpreterException {
		for (final Map.Entry<String, Object> entry : variables.entrySet()) {
			mLocalVariables.put(entry.getKey(), entry.getValue().getClass());
		}
		checkType(n);
	}
	
	private void checkType(final AtsASTNode n) throws InterpreterException {
		if (n instanceof AssignmentExpressionAST) {
			checkType((AssignmentExpressionAST) n);
		} else if (n instanceof BinaryExpressionAST) {
			checkType((BinaryExpressionAST) n);
		} else if (n instanceof ConditionalBooleanExpressionAST) {
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
			for (final AtsASTNode stmt : ((StatementListAST) n).getOutgoingNodes()) {
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
	
	private void checkType(final AssignmentExpressionAST as) throws InterpreterException {
		final List<AtsASTNode> children = as.getOutgoingNodes();
		final ILocation errorLocation = as.getLocation();
		if (children.size() != 2) {
			String message = "Assignment should have 2 operands." + LINE_SEPARATOR;
			message = message.concat("On the left-hand side there  must be a variable, ");
			message = message.concat("on the right-hand side there can be an arbitrary expression.");
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check the type of children
		checkType(children.get(0));
		checkType(children.get(1));
		
		final VariableExpressionAST var = (VariableExpressionAST) children.get(0);
		// Check whether the right-hand side has expected type.
		for (final Class<?> c : getTypes(children.get(1))) {
			children.get(1).setType(c);
			// Check for correct types
			if (AssignableTest.isAssignableFrom(var.getReturnType(), c)) {
				return;
			}
		}
		String message = "Right side has incorrect type." + LINE_SEPARATOR;
		message = message.concat(EXPECTED + var.getReturnType().getSimpleName() + GOT
				+ children.get(1).getReturnType().getSimpleName());
		final String longDescription = message;
		throw new InterpreterException(errorLocation, longDescription);
		
	}
	
	private void checkType(final BinaryExpressionAST be) throws InterpreterException {
		final List<AtsASTNode> children = be.getOutgoingNodes();
		final ILocation errorLocation = be.getLocation();
		if (children.size() != 2) {
			final String message = be.getOperatorAsString() + " should have 2 operands of type \"int\"."
					+ LINE_SEPARATOR + NUM_OF_OPERANDS + children.size();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check children for correct type
		checkType(children.get(0));
		checkType(children.get(1));
		
		// If the return type of this binary expression is 'String', we do
		// not need to type check the operands
		// because we just call the toString-Method of every operand.
		if (be.getReturnType() == String.class) {
			return;
		}
		
		// Check whether first child has expected type.
		boolean firstChildHasCorrectType = false;
		for (final Class<?> c : getTypes(children.get(0))) {
			if (AssignableTest.isAssignableFrom(be.getReturnType(), c)) {
				firstChildHasCorrectType = true;
			}
		}
		
		if (!firstChildHasCorrectType) {
			String message = "Left operand of \"" + be.getOperatorAsString() + "\" has incorrect type."
					+ LINE_SEPARATOR;
			message = message.concat(EXPECTED + be.getReturnType().getSimpleName() + GOT
					+ children.get(0).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		
		// Check whether second child has expected type.
		for (final Class<?> c : getTypes(children.get(1))) {
			if (AssignableTest.isAssignableFrom(be.getReturnType(), c)) {
				return;
			}
		}
		String message = "Right operand of \"" + be.getOperatorAsString() + "\" has incorrect type."
				+ LINE_SEPARATOR;
		message = message.concat(EXPECTED + be.getReturnType().getSimpleName() + GOT
				+ children.get(1).getReturnType().getSimpleName());
		final String longDescription = message;
		throw new InterpreterException(errorLocation, longDescription);
	}
	
	private void checkType(final ConditionalBooleanExpressionAST cbe) throws InterpreterException {
		final List<AtsASTNode> children = cbe.getOutgoingNodes();
		final ILocation errorLocation = cbe.getLocation();
		if ((cbe.getOperator() == ConditionalBooleanOperatorAST.NOT) && (children.size() != 1)) {
			final String message = "\"!\" operator should have 1 operand." + LINE_SEPARATOR
					+ NUM_OF_OPERANDS + children.size();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		} else if ((cbe.getOperator() == ConditionalBooleanOperatorAST.AND) && (children.size() != 2)) {
			final String message = "\"&&\" operator should have 2 operands." + LINE_SEPARATOR
					+ NUM_OF_OPERANDS + children.size();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		} else if ((cbe.getOperator() == ConditionalBooleanOperatorAST.OR) && (children.size() != 2)) {
			final String message = " \"||\" operator should have 2 operands." + LINE_SEPARATOR
					+ NUM_OF_OPERANDS + children.size();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check children for correct type
		checkType(children.get(0));
		if (children.size() == 2) {
			checkType(children.get(1));
		}
		// Check whether first child has type 'int'
		boolean firstChildHasCorrectType = false;
		for (final Class<?> c : getTypes(children.get(0))) {
			if (AssignableTest.isAssignableFrom(cbe.getReturnType(), c)) {
				firstChildHasCorrectType = true;
			}
		}
		if (!firstChildHasCorrectType) {
			String message = (children.size() == 2 ? "Left " : "") + "argument has incorrect type."
					+ LINE_SEPARATOR;
			message = message.concat(EXPECTED + cbe.getReturnType().getSimpleName() + GOT
					+ children.get(0).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check whether second child has type 'int'
		if (children.size() == 2) {
			for (final Class<?> c : getTypes(children.get(1))) {
				if (AssignableTest.isAssignableFrom(cbe.getReturnType(), c)) {
					return;
				}
			}
			String message = "Right argument has incorrect type." + LINE_SEPARATOR;
			message = message.concat(EXPECTED + cbe.getReturnType().getSimpleName() + GOT
					+ children.get(1).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
	}
	
	private static void checkType(final ForStatementAST fs) throws InterpreterException {
		final List<AtsASTNode> children = fs.getOutgoingNodes();
		final ILocation errorLocation = fs.getLocation();
		if (children.size() != NUMBER_OF_FOR_ARGUMENTS) {
			String message = "ForStatement should have 4 arguments (initStmt, condition, updateStmt) {stmtList}."
					+ LINE_SEPARATOR;
			message = message.concat("Num of children: " + children.size());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// First child is the loop condition.
		if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
			String message = "Loopcondition has incorrect type." + LINE_SEPARATOR;
			message = message.concat(EXPECTED + Boolean.class.getSimpleName() + GOT
					+ children.get(0).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
	}
	
	private void checkType(final IfElseStatementAST is) throws InterpreterException {
		final List<AtsASTNode> children = is.getOutgoingNodes();
		final ILocation errorLocation = is.getLocation();
		if (children.size() != NUMBER_OF_ITE_ARGUMENTS) {
			String message =
					"IfElseStatement should have 3 operands (Condition) { Thenstatements} {Elsestatements})"
							+ LINE_SEPARATOR;
			message = message.concat(NUM_OF_OPERANDS + children.size());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check the children for correct type.
		checkType(children.get(0));
		// Check if the if-condition has type Boolean.
		if (children.get(0).getReturnType() != Boolean.class) {
			String message = CONDITION_HAS_INCORRECT_TYPE + LINE_SEPARATOR;
			message = message.concat(EXPECTED + Boolean.class.getSimpleName() + GOT
					+ children.get(0).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
	}
	
	private void checkType(final IfStatementAST is) throws InterpreterException {
		final List<AtsASTNode> children = is.getOutgoingNodes();
		final ILocation errorLocation = is.getLocation();
		if (children.size() != 2) {
			String message = "IfStatement should have 2 operands (condition) {thenStatements}"
					+ LINE_SEPARATOR;
			message = message.concat(NUM_OF_OPERANDS + children.size());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check the first child for correct type
		checkType(children.get(0));
		// Check if the if-condition has type Boolean.
		if (children.get(0).getReturnType() != Boolean.class) {
			String message = CONDITION_HAS_INCORRECT_TYPE + LINE_SEPARATOR;
			message = message.concat(
					EXPECTED + Boolean.class.getSimpleName() + GOT + children.get(0).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
	}
	
	private void checkType(final OperationInvocationExpressionAST oe) throws InterpreterException {
		final ILocation errorLocation = oe.getLocation();
		final String opName = oe.getOperationName();
		if (!mExistingOperations.containsKey(opName) && !opName.equals(TestFileInterpreter.ASSERT)
				&& !opName.equals(TestFileInterpreter.PRINT) && !opName.equals(TestFileInterpreter.WRITE)) {
			final String shortDescr = "Unsupported operation \"" + oe.getOperationName() + "\"";
			final String shortDescription = shortDescr;
			final String allOperations = (new ListExistingOperations(mExistingOperations)).prettyPrint();
			String longDescr;
			if (!Character.isLowerCase(opName.charAt(0))) {
				longDescr = "Operation names have to start with a lowercase letter." + LINE_SEPARATOR;
			} else {
				longDescr = "";
			}
			longDescr +="We support only the following operations " + LINE_SEPARATOR + allOperations;
			final String longDescription = longDescr;
			throw new InterpreterException(errorLocation, shortDescription, longDescription);
		}
		// Check the arguments of this operation for correct type.
		if ((oe.getOutgoingNodes() != null) && (oe.getOutgoingNodes().get(0) != null)) {
			for (final AtsASTNode n : oe.getOutgoingNodes().get(0).getOutgoingNodes()) {
				checkType(n);
			}
		}
		if (opName.equals(TestFileInterpreter.PRINT)) {
			return;
		}
		/*
		 * Set type of this operation, because until now, it didn't have any type. It is not relevant for further
		 * type checking results, but it avoids NullPointerExceptions.
		 */
		final Set<Class<?>> types = getTypes(oe);
		if (!types.isEmpty()) {
			Class<?>[] arr = new Class<?>[1];
			arr = types.toArray(arr);
			oe.setType(arr[0]);
		}
		
	}
	
	private void checkType(final RelationalExpressionAST re) throws InterpreterException {
		final List<AtsASTNode> children = re.getOutgoingNodes();
		final ILocation errorLocation = re.getLocation();
		if (children.size() != 2) {
			final String message = "\"" + re.getOperatorAsString() + " should have 2 operands."
					+ LINE_SEPARATOR + NUM_OF_OPERANDS + children.size();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check children for correct type
		checkType(children.get(0));
		checkType(children.get(1));
		// Check whether first child has expected type.
		boolean firstChildHasCorrectType = false;
		for (final Class<?> c : getTypes(children.get(0))) {
			if (AssignableTest.isAssignableFrom(re.getExpectingType(), c)) {
				firstChildHasCorrectType = true;
			}
		}
		if (!firstChildHasCorrectType) {
			String message = "Left operand has incorrect type." + LINE_SEPARATOR;
			message = message.concat(EXPECTED + re.getExpectingType().getSimpleName() + GOT
					+ children.get(0).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check whether second child has expected type.
		for (final Class<?> c : getTypes(children.get(1))) {
			if (AssignableTest.isAssignableFrom(re.getExpectingType(), c)) {
				return;
			}
		}
		String message = "Right operand has incorrect type." + LINE_SEPARATOR;
		message = message.concat(EXPECTED + re.getExpectingType().getSimpleName() + GOT
				+ children.get(1).getReturnType().getSimpleName());
		final String longDescription = message;
		throw new InterpreterException(errorLocation, longDescription);
	}
	
	private void checkType(final UnaryExpressionAST ue) throws InterpreterException {
		final List<AtsASTNode> children = ue.getOutgoingNodes();
		final ILocation errorLocation = ue.getLocation();
		if (children.size() != 1) {
			final String message = "\"" + ue.getOperatorAsString() + "\" should have one variable as argument."
					+ LINE_SEPARATOR + "Num of arguments: " + children.size();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check children for correct type
		checkType(children.get(0));
		
		if (!(children.get(0) instanceof VariableExpressionAST)) {
			final String message = "Unary operators are applicable only on variables."
					+ LINE_SEPARATOR + "You want to apply it on "
					+ children.get(0).getClass().getSimpleName();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		// Check if variable has expected type, namely
		// type 'int'
		for (final Class<?> c : getTypes(children.get(0))) {
			if (AssignableTest.isAssignableFrom(ue.getExpectingType(), c)) {
				return;
			}
		}
		String message = "Operand has incorrect type." + LINE_SEPARATOR;
		message = message.concat(EXPECTED + ue.getExpectingType().getSimpleName() + GOT
				+ children.get(0).getReturnType().getSimpleName());
		final String longDescription = message;
		throw new InterpreterException(errorLocation, longDescription);
	}
	
	private void checkType(final VariableExpressionAST v) throws InterpreterException {
		final ILocation errorLocation = v.getLocation();
		if (mLocalVariables.containsKey(v.getIdentifier())) {
			v.setType(mLocalVariables.get(v.getIdentifier()));
		} else {
			final String shortDescription = "Undeclared variable";
			// String message = "Variable \"" + v.getIdentifier() +
			// "\" at line " + v.getLocation().getStartLine()
			// + " was not declared.";
			final String longDescription = "Variable \"" + v.getIdentifier() + "\" was not declared.";
			throw new InterpreterException(errorLocation, shortDescription, longDescription);
		}
	}
	
	private void checkType(final VariableDeclarationAST vd) throws InterpreterException {
		final List<AtsASTNode> children = vd.getOutgoingNodes();
		final ILocation errorLocation = vd.getLocation();
		if (children.size() > 1) {
			final String message = "Variabledeclaration can have at most one operand. (the value to assign)";
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		for (final String id : vd.getIdentifiers()) {
			mLocalVariables.put(id, vd.getExpectingType());
		}
		// if the variable doesn't get assigned a value, then return.
		if (children.isEmpty()) {
			return;
		}
		
		// Check type of the right-hand side of the variable assignment.
		checkType(children.get(0));
		for (final Class<?> c : getTypes(children.get(0))) {
			if (AssignableTest.isAssignableFrom(vd.getReturnType(), c)) {
				return;
			}
		}
		final String message =
				"Operand on the right side has incorrect type." + LINE_SEPARATOR
						+ EXPECTED + vd.getExpectingType().getSimpleName() + GOT
						+ children.get(0).getReturnType().getSimpleName();
		final String longDescription = message;
		throw new InterpreterException(errorLocation, longDescription);
	}
	
	private static void checkType(final WhileStatementAST ws) throws InterpreterException {
		final List<AtsASTNode> children = ws.getOutgoingNodes();
		final ILocation errorLocation = ws.getLocation();
		if (children.size() != 2) {
			String message = "WhileStatement should have 2 operands (condition) {stmtList}"
					+ LINE_SEPARATOR;
			message = message.concat("Number of children: " + children.size());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
			String message = CONDITION_HAS_INCORRECT_TYPE + LINE_SEPARATOR;
			message = message.concat(EXPECTED + Boolean.class.getSimpleName() + GOT
					+ children.get(0).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
	}
	
	/**
	 * Returns the possible types for the given AST node. Only operations can potentially have more return types,
	 * because there could operations with different return types, but with the same name.
	 * <p>
	 * Throws an {@link UnsupportedOperationException} if the operation was not found, or if the operation has no
	 * declared method called "getResult".
	 * 
	 * @param n
	 *            the AtsAST node
	 * @return a set of types, where the set could contain more than 1 element if the given node represents an
	 *         operation invocation, otherwise it contains only 1 element.
	 */
	private Set<Class<?>> getTypes(final AtsASTNode n) {
		if (n instanceof OperationInvocationExpressionAST) {
			final OperationInvocationExpressionAST oe = (OperationInvocationExpressionAST) n;
			final String opName = oe.getOperationName();
			final Set<Class<?>> returnTypes = new HashSet<>();
			if (opName.equals(TestFileInterpreter.PRINT) || opName.equals(TestFileInterpreter.ASSERT)
					|| opName.equals(TestFileInterpreter.WRITE)) {
				return returnTypes;
			}
			if (!mExistingOperations.containsKey(opName)) {
				throw new UnsupportedOperationException("Operation \"" + opName + "\" was not found!");
			}
			final Set<Class<?>> operationClasses = mExistingOperations.get(opName);
			for (final Class<?> operationClass : operationClasses) {
				for (final Method m : operationClass.getMethods()) {
					if ("getResult".equals(m.getName())) {
						returnTypes.add(m.getReturnType());
					}
				}
			}
			if (returnTypes.isEmpty()) {
				throw new UnsupportedOperationException("Operation \"" + opName
						+ "\" has no operation \"getResult()\"");
			}
			return returnTypes;
			
		}
		final Set<Class<?>> returnType = new HashSet<>();
		returnType.add(n.getReturnType());
		return returnType;
	}
}
