/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.FileLocator;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AutomataScriptInterpreterOverallResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AutomataScriptInterpreterOverallResult.OverallResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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

/**
 * This enum represents the current flow of the program. It could have the values "NORMAL", "BREAK", "CONTINUE", and
 * "RETURN". It is necessary to implement the "continue" and "break" function for loops.
 * 
 * @author musab@informatik.uni-freiburg.de
 */
enum Flow {
	NORMAL,
	BREAK,
	CONTINUE,
	RETURN;
}

/**
 * This is the main class for interpreting automata script test files. It fulfills the following tasks: - Interpreting
 * automata definitions - Type checking the automata script test file - Interpreting the automata script test file -
 * Generation and output of the results
 * 
 * @author musab@informatik.uni-freiburg.de
 */
public class TestFileInterpreter implements IMessagePrinter {
	
	/**
	 * This class implements a static type checker for the automatascript files.
	 * 
	 * @author musab@informatik.uni-freiburg.de
	 */
	class AutomataScriptTypeChecker {
		/**
		 * A map from variable names to the type they represent. This is needed to check for type conformity, e.g.
		 * variable assignment.
		 */
		private final Map<String, Class<?>> mLocalVariables = new HashMap<String, Class<?>>();
		
		/**
		 * Checks the test file for type errors and for undeclared variables.
		 * 
		 * @param n
		 *            the root node of the AST
		 * @throws InterpreterException
		 */
		public void checkTestFile(final AtsASTNode n) throws InterpreterException {
			for (final Map.Entry<String, Object> entry : mVariables.entrySet()) {
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
				String message = "Assignment should have 2 operands." + System.getProperty("line.separator");
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
			String message = "Right side has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + var.getReturnType().getSimpleName() + "\tGot: "
					+ children.get(1).getReturnType().getSimpleName() + "");
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
			
		}
		
		private void checkType(final BinaryExpressionAST be) throws InterpreterException {
			final List<AtsASTNode> children = be.getOutgoingNodes();
			final ILocation errorLocation = be.getLocation();
			if (children.size() != 2) {
				final String message = be.getOperatorAsString() + " should have 2 operands of type \"int\"."
						+ System.getProperty("line.separator") + "Num of operands: " + children.size();
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
						+ System.getProperty("line.separator");
				message = message.concat("Expected: " + be.getReturnType().getSimpleName() + "\tGot: "
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
					+ System.getProperty("line.separator");
			message = message.concat("Expected: " + be.getReturnType().getSimpleName() + "\tGot: "
					+ children.get(1).getReturnType().getSimpleName() + "");
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		
		private void checkType(final ConditionalBooleanExpressionAST cbe) throws InterpreterException {
			final List<AtsASTNode> children = cbe.getOutgoingNodes();
			final ILocation errorLocation = cbe.getLocation();
			if ((cbe.getOperator() == ConditionalBooleanOperatorAST.NOT) && (children.size() != 1)) {
				final String message = "\"!\" operator should have 1 operand." + System.getProperty("line.separator")
						+ "Num of operands: " + children.size();
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			} else if ((cbe.getOperator() == ConditionalBooleanOperatorAST.AND) && (children.size() != 2)) {
				final String message = "\"&&\" operator should have 2 operands." + System.getProperty("line.separator")
						+ "Num of operands: " + children.size();
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			} else if ((cbe.getOperator() == ConditionalBooleanOperatorAST.OR) && (children.size() != 2)) {
				final String message = " \"||\" operator should have 2 operands." + System.getProperty("line.separator")
						+ "Num of operands: " + children.size();
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
						+ System.getProperty("line.separator");
				message = message.concat("Expected: " + cbe.getReturnType().getSimpleName() + "\tGot: "
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
				String message = "Right argument has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + cbe.getReturnType().getSimpleName() + "\tGot: "
						+ children.get(1).getReturnType().getSimpleName());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		private void checkType(final ForStatementAST fs) throws InterpreterException {
			final List<AtsASTNode> children = fs.getOutgoingNodes();
			final ILocation errorLocation = fs.getLocation();
			if (children.size() != 4) {
				String message = "ForStatement should have 4 arguments (initStmt, condition, updateStmt) {stmtList}."
						+ System.getProperty("line.separator");
				message = message.concat("Num of children: " + children.size());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// First child is the loop condition.
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = "Loopcondition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: "
						+ children.get(0).getReturnType().getSimpleName());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		private void checkType(final IfElseStatementAST is) throws InterpreterException {
			final List<AtsASTNode> children = is.getOutgoingNodes();
			final ILocation errorLocation = is.getLocation();
			if (children.size() != 3) {
				String message =
						"IfElseStatement should have 3 operands (Condition) { Thenstatements} {Elsestatements})"
								+ System.getProperty("line.separator");
				message = message.concat("Num of operands: " + children.size());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check the children for correct type.
			checkType(children.get(0));
			// Check if the if-condition has type Boolean.
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: "
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
						+ System.getProperty("line.separator");
				message = message.concat("Num of operands: " + children.size());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check the first child for correct type
			checkType(children.get(0));
			// Check if the if-condition has type Boolean.
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: "
						+ children.get(0).getReturnType().getSimpleName());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		private void checkType(final OperationInvocationExpressionAST oe) throws InterpreterException {
			final ILocation errorLocation = oe.getLocation();
			final String opName = oe.getOperationName().toLowerCase();
			if (!mExistingOperations.containsKey(opName)) {
				if (!opName.equals("assert") && !opName.equals("print") && !opName.equals("write")) {
					final String shortDescr = "Unsupported operation \"" + oe.getOperationName() + "\"";
					final String shortDescription = shortDescr;
					final String allOperations = (new ListExistingOperations(mExistingOperations)).prettyPrint();
					final String longDescr = "We support only the following operations "
							+ System.getProperty("line.separator") + allOperations;
					final String longDescription = longDescr;
					throw new InterpreterException(errorLocation, shortDescription, longDescription);
				}
			}
			// Check the arguments of this operation for correct type.
			if ((oe.getOutgoingNodes() != null) && (oe.getOutgoingNodes().get(0) != null)) {
				for (final AtsASTNode n : oe.getOutgoingNodes().get(0).getOutgoingNodes()) {
					checkType(n);
				}
			}
			if (opName.equals("print")) {
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
						+ System.getProperty("line.separator") + "Num of operands: " + children.size();
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
				String message = "Left operand has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + re.getExpectingType().getSimpleName() + "\tGot: "
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
			String message = "Right operand has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + re.getExpectingType().getSimpleName() + "\tGot: "
					+ children.get(1).getReturnType().getSimpleName());
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		
		private void checkType(final UnaryExpressionAST ue) throws InterpreterException {
			final List<AtsASTNode> children = ue.getOutgoingNodes();
			final ILocation errorLocation = ue.getLocation();
			if (children.size() != 1) {
				final String message = "\"" + ue.getOperatorAsString() + "\" should have one variable as argument."
						+ System.getProperty("line.separator") + "Num of arguments: " + children.size();
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			// Check children for correct type
			checkType(children.get(0));
			
			if (!(children.get(0) instanceof VariableExpressionAST)) {
				final String message = "Unary operators are applicable only on variables."
						+ System.getProperty("line.separator") + "You want to apply it on "
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
			String message = "Operand has incorrect type." + System.getProperty("line.separator");
			message = message.concat("Expected: " + ue.getExpectingType().getSimpleName() + "\tGot: "
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
			if ((children.size() != 0) && (children.size() != 1)) {
				final String message = "Variabledeclaration can have at most one operand. (the value to assign)";
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			for (final String id : vd.getIdentifiers()) {
				mLocalVariables.put(id, vd.getExpectingType());
			}
			// if the variable doesn't get assigned a value, then return.
			if (children.size() == 0) {
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
					"Operand on the right side has incorrect type." + System.getProperty("line.separator")
							+ "Expected: " + vd.getExpectingType().getSimpleName() + "\tGot: "
							+ children.get(0).getReturnType().getSimpleName();
			final String longDescription = message;
			throw new InterpreterException(errorLocation, longDescription);
		}
		
		private void checkType(final WhileStatementAST ws) throws InterpreterException {
			final List<AtsASTNode> children = ws.getOutgoingNodes();
			final ILocation errorLocation = ws.getLocation();
			if (children.size() != 2) {
				String message = "WhileStatement should have 2 operands (condition) {stmtList}"
						+ System.getProperty("line.separator");
				message = message.concat("Number of children: " + children.size());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = "Condition has incorrect type." + System.getProperty("line.separator");
				message = message.concat("Expected: " + Boolean.class.getSimpleName() + "\tGot: "
						+ children.get(0).getReturnType().getSimpleName());
				final String longDescription = message;
				throw new InterpreterException(errorLocation, longDescription);
			}
		}
		
		/**
		 * Returns the possible types for the given AST node. Only operations can potentially have more return types,
		 * because there could operations with different return types, but with the same name.
		 * 
		 * @param n
		 *            the AtsAST node
		 * @return a set of types, where the set could contain more than 1 element if the given node represents an
		 *         operation invocation, otherwise it contains only 1 element.
		 * @throws UnsupportedOperationException
		 *             if the operation was not found, or if the operation has no declared method called "getResult".
		 */
		private Set<Class<?>> getTypes(final AtsASTNode n) throws UnsupportedOperationException {
			if (n instanceof OperationInvocationExpressionAST) {
				final OperationInvocationExpressionAST oe = (OperationInvocationExpressionAST) n;
				final String opName = oe.getOperationName().toLowerCase();
				final Set<Class<?>> returnTypes = new HashSet<Class<?>>();
				if (opName.equals("print") || opName.equals("assert") || opName.equals("write")) {
					return returnTypes;
				}
				if (mExistingOperations.containsKey(opName)) {
					final Set<Class<?>> operationClasses = mExistingOperations.get(opName);
					for (final Class<?> operationClass : operationClasses) {
						for (final Method m : operationClass.getMethods()) {
							if (m.getName().equals("getResult")) {
								returnTypes.add(m.getReturnType());
							}
						}
					}
					if (returnTypes.isEmpty()) {
						throw new UnsupportedOperationException("Operation \"" + opName
								+ "\" has no operation \"getResult()\"");
					} else {
						return returnTypes;
					}
				} else {
					throw new UnsupportedOperationException("Operation \"" + opName + "\" was not found!");
				}
			} else {
				final Set<Class<?>> returnType = new HashSet<Class<?>>();
				returnType.add(n.getReturnType());
				return returnType;
			}
		}
		
	}
	
	/**
	 * Contains the declared variables, automata variables too. It is a map from variable name to the object it
	 * represents.
	 */
	private final Map<String, Object> mVariables;
	/**
	 * Contains current existing automata operations. It is a map from operation name to a set of class types, because
	 * there might be operations with the same name, but with different parameter types and in different packages. e.g.
	 * Accepts for NestedWord automata and Accepts for Petri nets.
	 */
	private final Map<String, Set<Class<?>>> mExistingOperations;
	/**
	 * The current flow of the program.
	 */
	private Flow mFlow;
	/**
	 * Our interpreter for automata definitions.
	 */
	private final AutomataDefinitionInterpreter mAutomataInterpreter;
	/**
	 * Our type checker for the automatascript file.
	 */
	private final AutomataScriptTypeChecker mTypeChecker;
	private final ILogger mLogger;
	/**
	 * The automaton, which was lastly printed by a print operation.
	 */
	private IAutomaton<?, ?> mLastPrintedAutomaton;
	/**
	 * Indicates whether the automaton, which is output by a print operation, should also be printed to a .ats-file.
	 */
	private boolean mPrintAutomataToFile;
	private PrintWriter mPrintWriter;
	private String mPath = ".";
	/**
	 * Indicates whether all commands in .ats file(s) should be ignored and instead the specified command should be
	 * executed.
	 */
	private boolean mIgnoreOperationsAndExecuteCommandInstead;
	private String mCommandToExecute;
	
	public enum LoggerSeverity {
		INFO,
		WARNING,
		ERROR,
		DEBUG
	};
	
	private enum Finished {
		FINISHED,
		TIMEOUT,
		ERROR,
		OUTOFMEMORY
	};
	
	public static final String sAssertionHoldsMessage = "Assertion holds.";
	public static final String sAssertionViolatedMessage = "Assertion violated!";
	
	/**
	 * If an error occurred during the interpretation this is set to true and further interpretation is aborted.
	 */
	private final List<GenericResultAtElement<AtsASTNode>> mResultOfAssertStatements;
	private final IUltimateServiceProvider mServices;
	private final boolean mProvideStatisticsResults = true;
	
	public TestFileInterpreter(final IUltimateServiceProvider services) {
		assert services != null;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		readPreferences();
		mVariables = new HashMap<String, Object>();
		mFlow = Flow.NORMAL;
		mAutomataInterpreter = new AutomataDefinitionInterpreter(this, mLogger, mServices);
		mTypeChecker = new AutomataScriptTypeChecker();
		mExistingOperations = getOperationClasses();
		mLastPrintedAutomaton = null;
		mResultOfAssertStatements = new ArrayList<GenericResultAtElement<AtsASTNode>>();
		if (mPrintAutomataToFile) {
			final String path = mPath + File.separator + "automatascriptOutput" + getDateTime() + ".ats";
			final File file = new File(path);
			try {
				final FileWriter writer = new FileWriter(file);
				mPrintWriter = new PrintWriter(writer);
			} catch (final IOException e) {
				throw new AssertionError(e);
			}
		}
	}
	
	private void readPreferences() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mPrintAutomataToFile = prefs.getBoolean(PreferenceInitializer.Name_WriteToFile);
		mPath = prefs.getString(PreferenceInitializer.Name_Path);
		mIgnoreOperationsAndExecuteCommandInstead = prefs.getBoolean(PreferenceInitializer.Name_ExecuteCommandFlag);
		mCommandToExecute = prefs.getString(PreferenceInitializer.Name_ExecuteCommandString);
	}
	
	private static String getDateTime() {
		final DateFormat dateFormat = new SimpleDateFormat("yyyyMMddHHmmss");
		final Date date = new Date();
		return dateFormat.format(date);
	}
	
	/**
	 * Method to interpret an automatascript test file. The interpretation is done in 4 steps. Step 1: Interpret
	 * automata defintions. Step 2: Check the automatascript test file for correct types and undeclared variables. (Type
	 * checking) Step 3: Interpret the automatascript test file. Step 4: Report the results to the ILogger and to the
	 * web interface.
	 * 
	 * @param node
	 *            the root node of the AST
	 * @return the result of the automatascript test file, which is either an automaton or null.
	 */
	public Object interpretTestFile(final AtsASTNode node) {
		AutomataTestFileAST ats = null;
		if (node instanceof AutomataTestFileAST) {
			ats = (AutomataTestFileAST) node;
		}
		Finished interpretationFinished = Finished.FINISHED;
		String errorMessage = null;
		reportToLogger(LoggerSeverity.DEBUG, "Interpreting automata definitions...");
		// Interpret automata definitions
		try {
			mAutomataInterpreter.interpret(ats.getAutomataDefinitions());
		} catch (final Exception e) {
			reportToLogger(LoggerSeverity.INFO, "Error during interpreting automata definitions.");
			reportToLogger(LoggerSeverity.INFO, "Error: " + e.getMessage());
			if (e instanceof InterpreterException) {
				reportToLogger(LoggerSeverity.INFO, "Error: " + ((InterpreterException) e).getShortDescription());
			}
			reportToLogger(LoggerSeverity.INFO, "Interpretation of testfile cancelled.");
			reportToUltimate(Severity.ERROR, e.getMessage() + " Interpretation of testfile cancelled.", "Error", node);
			interpretationFinished = Finished.ERROR;
			errorMessage = e.getMessage();
		}
		
		final AtsASTNode statements;
		if (mIgnoreOperationsAndExecuteCommandInstead) {
			// TODO here we need the interpreted command, how? for now, nothing happens
			statements = null;
		} else {
			statements = ats.getStatementList();
		}
		
		if (interpretationFinished == Finished.FINISHED) {
			// Put all defined automata into variables map
			mVariables.putAll(mAutomataInterpreter.getAutomata());
			reportToLogger(LoggerSeverity.DEBUG, "Typechecking of test file...");
			// Type checking
			try {
				mTypeChecker.checkTestFile(statements);
			} catch (final InterpreterException e) {
				reportToLogger(LoggerSeverity.INFO, "Error: " + e.getMessage());
				if (e instanceof InterpreterException) {
					reportToLogger(LoggerSeverity.INFO, "Error: " + e.getShortDescription());
				}
				reportToLogger(LoggerSeverity.INFO, "Interpretation of testfile cancelled.");
				String shortDescription = e.getShortDescription();
				if (shortDescription == null) {
					shortDescription = "Error";
				}
				reportToUltimate(Severity.ERROR, e.getLongDescription(), shortDescription, node);
				interpretationFinished = Finished.ERROR;
				errorMessage = e.getLongDescription();
			}
		}
		
		Object result = null;
		if (interpretationFinished == Finished.FINISHED) {
			// Interpreting test file
			reportToLogger(LoggerSeverity.DEBUG, "Interpreting test file...");
			if (statements == null) {
				// File contains only automata definitions no testcases.
				result = null;
			} else {
				try {
					result = interpret(statements);
				} catch (final InterpreterException e) {
					final Throwable cause = e.getCause();
					if (cause != null) {
						if (cause instanceof AutomataOperationCanceledException) {
							interpretationFinished = Finished.TIMEOUT;
						} else if (cause instanceof OutOfMemoryError) {
							interpretationFinished = Finished.OUTOFMEMORY;
						} else {
							interpretationFinished = Finished.ERROR;
							errorMessage = e.getLongDescription();
						}
					} else {
						interpretationFinished = Finished.ERROR;
						errorMessage = e.getLongDescription();
					}
					printMessage(Severity.ERROR, LoggerSeverity.INFO, e.getLongDescription(),
							"Interpretation of ats file failed", node);
				}
			}
		}
		reportToLogger(LoggerSeverity.DEBUG, "Reporting results...");
		reportResult(interpretationFinished, errorMessage);
		if (mPrintAutomataToFile) {
			mPrintWriter.close();
		}
		return result;
	}
	
	/**
	 * Gets the automaton which was lastly printed by a print-operation.
	 * 
	 * @return
	 */
	public IAutomaton<?, ?> getLastPrintedAutomaton() {
		return mLastPrintedAutomaton;
	}
	
	private Object interpret(final AssignmentExpressionAST as) throws InterpreterException {
		final List<AtsASTNode> children = as.getOutgoingNodes();
		final VariableExpressionAST var = (VariableExpressionAST) children.get(0);
		if (!mVariables.containsKey(var.getIdentifier())) {
			final String message = as.getLocation().getStartLine() + ": Variable \"" + var.getIdentifier()
					+ "\" was not declared before.";
			throw new InterpreterException(as.getLocation(), message);
		}
		final Object oldValue = mVariables.get(var.getIdentifier());
		final Object newValue = interpret(children.get(1));
		
		if (newValue == null) {
			final String longDescr = "Var \"" + var.getIdentifier() + "\" is assigned \"null\".";
			throw new InterpreterException(as.getLocation(), longDescr);
		}
		
		switch (as.getOperator()) {
			case ASSIGN:
				mVariables.put(var.getIdentifier(), newValue);
				break;
			case PLUSASSIGN: {
				final Integer assignValue = ((Integer) oldValue) + ((Integer) newValue);
				mVariables.put(var.getIdentifier(), assignValue);
				break;
			}
			case MINUSASSIGN: {
				final Integer assignValue = ((Integer) oldValue) - ((Integer) newValue);
				mVariables.put(var.getIdentifier(), assignValue);
				break;
			}
			case MULTASSIGN: {
				final Integer assignValue = ((Integer) oldValue) * ((Integer) newValue);
				mVariables.put(var.getIdentifier(), assignValue);
				break;
			}
			case DIVASSIGN: {
				final Integer assignValue = ((Integer) oldValue) / ((Integer) newValue);
				mVariables.put(var.getIdentifier(), assignValue);
				break;
			}
			default: {
				throw new InterpreterException(as.getLocation(),
						"AssignmentExpression: This type of operator is not supported: " + as.getOperator());
			}
			
		}
		return oldValue;
	}
	
	private Object interpret(final AtsASTNode node) throws InterpreterException {
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
	
	private Object interpret(final BinaryExpressionAST be) throws InterpreterException {
		final List<AtsASTNode> children = be.getOutgoingNodes();
		// If the return type is 'String', we just call the toString method of
		// each operand
		// and return the concatenation of these strings.
		if (be.getReturnType() == String.class) {
			String result = interpret(children.get(0)).toString();
			result = result.concat(interpret(children.get(1)).toString());
			return result;
		}
		final Integer v1 = (Integer) interpret(children.get(0));
		final Integer v2 = (Integer) interpret(children.get(1));
		
		switch (be.getOperator()) {
			case PLUS:
				return v1 + v2;
			case MINUS:
				return v1 - v2;
			case MULTIPLICATION:
				return v1 * v2;
			case DIVISION:
				return v1 / v2;
			default:
				throw new InterpreterException(be.getLocation(),
						" BinaryExpression: This type of operator is not supported: " + be.getOperator());
		}
	}
	
	private Object interpret(final BreakStatementAST bst) {
		// Change the flow
		mFlow = Flow.BREAK;
		return null;
	}
	
	private Boolean interpret(final ConditionalBooleanExpressionAST cbe) throws InterpreterException {
		final List<AtsASTNode> children = cbe.getOutgoingNodes();
		switch (cbe.getOperator()) {
			case NOT:
				return !((Boolean) interpret(children.get(0)));
			case AND: {
				final Boolean v1 = (Boolean) interpret(children.get(0));
				if (!v1) {
					return false;
				} // Short-circuit and
				final Boolean v2 = (Boolean) interpret(children.get(1));
				return v2;
			}
			case OR: {
				final Boolean v1 = (Boolean) interpret(children.get(0));
				if (v1) {
					return true;
				} // Short-circuit or
				final Boolean v2 = (Boolean) interpret(children.get(1));
				return v2;
			}
			default: {
				final String message = "ConditionalBooleanExpression: This type of operator is not supported: "
						+ cbe.getOperator();
				throw new InterpreterException(cbe.getLocation(), message);
			}
		}
	}
	
	private Object interpret(final ConstantExpressionAST ce) {
		return ce.getValue();
	}
	
	private Object interpret(final ContinueStatementAST cst) {
		// Change the flow
		mFlow = Flow.CONTINUE;
		return null;
	}
	
	private Object interpret(final ForStatementAST fs) throws InterpreterException {
		final List<AtsASTNode> children = fs.getOutgoingNodes();
		
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
				final List<AtsASTNode> statementList = children.get(3).getOutgoingNodes();
				secondLoop: for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (mFlow != Flow.NORMAL) {
						switch (mFlow) {
							case BREAK:
							case RETURN: {
								mFlow = Flow.NORMAL;
								return null;
							}
							case CONTINUE: {
								mFlow = Flow.NORMAL;
								break secondLoop;
							}
							default:
								throw new UnsupportedOperationException();
						}
					}
				}
				// execute the updatestatement
				if (children.get(2) != null) {
					interpret(children.get(2));
				}
			}
		} else {
			for (; (Boolean) interpret(children.get(0));) {
				final List<AtsASTNode> statementList = children.get(3).getOutgoingNodes();
				secondLoop: for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (mFlow != Flow.NORMAL) {
						switch (mFlow) {
							case BREAK:
							case RETURN: {
								mFlow = Flow.NORMAL;
								return null;
							}
							case CONTINUE: {
								mFlow = Flow.NORMAL;
								break secondLoop;
							}
							default:
								throw new UnsupportedOperationException();
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
	
	private Object interpret(final IfElseStatementAST is) throws InterpreterException {
		final List<AtsASTNode> children = is.getOutgoingNodes();
		
		// children(0) is the condition
		if ((Boolean) interpret(children.get(0))) {
			interpret(children.get(1));
		} else {
			interpret(children.get(2));
		}
		return null;
	}
	
	private Object interpret(final IfStatementAST is) throws InterpreterException {
		final List<AtsASTNode> children = is.getOutgoingNodes();
		if ((Boolean) interpret(children.get(0))) {
			for (int i = 1; i < children.size(); i++) {
				interpret(children.get(i));
			}
		}
		return null;
	}
	
	private NestedWord<String> interpret(final NestedwordAST nw) {
		return new NestedWord<String>(nw.getWordSymbols(), nw.getNestingRelation());
	}
	
	private NestedLassoWord<String> interpret(final NestedLassowordAST nw) {
		final NestedWord<String> stem = interpret(nw.getStem());
		final NestedWord<String> loop = interpret(nw.getLoop());
		return new NestedLassoWord<String>(stem, loop);
	}
	
	private Object interpret(final OperationInvocationExpressionAST oe) throws InterpreterException {
		final List<AtsASTNode> children = oe.getOutgoingNodes();
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
					mResultOfAssertStatements.add(new GenericResultAtElement<AtsASTNode>(oe, Activator.PLUGIN_ID,
							mServices.getBacktranslationService(), sAssertionHoldsMessage, oe.getAsString(),
							Severity.INFO));
				} else {
					mResultOfAssertStatements.add(new GenericResultAtElement<AtsASTNode>(oe, Activator.PLUGIN_ID,
							mServices.getBacktranslationService(), sAssertionViolatedMessage, oe.getAsString(),
							Severity.ERROR));
				}
			} else {
				throw new AssertionError("assert expects boolean result, type checker should have found this");
			}
		} else if (oe.getOperationName().equalsIgnoreCase("print")) {
			final String argsAsString = children.get(0).getAsString();
			// ILocation loc = children.get(0).getLocation();
			reportToLogger(LoggerSeverity.INFO, "Printing " + argsAsString);
			final String text;
			if (arguments.get(0) instanceof IAutomaton) {
				final Format format;
				if (arguments.size() == 1) {
					format = Format.ATS;
				} else if (arguments.size() == 2) {
					if (arguments.get(1) instanceof String) {
						try {
							format = Format.valueOf((String) arguments.get(1));
						} catch (final Exception e) {
							throw new InterpreterException(oe.getLocation(),
									"unknown format " + (String) arguments.get(1));
						}
					} else {
						throw new InterpreterException(oe.getLocation(),
								"if first argument of print command is an "
										+ "automaton second argument has to be a string "
										+ "that defines an output format");
					}
				} else {
					throw new InterpreterException(oe.getLocation(),
							"if first argument of print command is an "
									+ "automaton only two arguments are allowed");
				}
				mLastPrintedAutomaton = (IAutomaton<?, ?>) arguments.get(0);
				text = (new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices),
						"automaton", format, mLastPrintedAutomaton))
								.getDefinitionAsString();
			} else {
				if (arguments.size() > 1) {
					throw new InterpreterException(oe.getLocation(),
							"if first argument of print command is not an "
									+ "automaton no second argument allowed");
				} else {
					text = String.valueOf(arguments.get(0));
				}
			}
			printMessage(Severity.INFO, LoggerSeverity.INFO, text, oe.getAsString(), oe);
			if (mPrintAutomataToFile) {
				final String comment = "/* " + oe.getAsString() + " */";
				mPrintWriter.println(comment);
				mPrintWriter.println(text);
			}
		} else if (oe.getOperationName().equalsIgnoreCase("write")) {
			if (arguments.size() != 3) {
				throw new InterpreterException(oe.getLocation(), "write needs three arguments");
			}
			final IAutomaton<String, String> automaton = (IAutomaton<String, String>) arguments.get(0);
			final String filename = (String) arguments.get(1);
			final Format format;
			final String formatAsString = (String) arguments.get(2);
			try {
				format = Format.valueOf(formatAsString);
			} catch (final Exception e) {
				throw new InterpreterException(oe.getLocation(),
						"unknown format " + (String) arguments.get(1));
			}
			final String argsAsString = children.get(0).getAsString();
			reportToLogger(LoggerSeverity.INFO,
					"Writing " + argsAsString + " to file " + filename + " in " + format + " format.");
			new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices), "ats", filename,
					format, "output according to \"write\" command", automaton);
		} else {
			final SimpleTimer timer = new SimpleTimer();
			final IOperation<String, String> op = getAutomataOperation(oe, arguments);
			if (op != null) {
				try {
					if (mProvideStatisticsResults) {
						mLogger.info("reporting benchmark results");
						AutomataOperationStatistics statistics = op.getAutomataOperationStatistics();
						if (statistics == null) {
							statistics = new AutomataOperationStatistics();
						}
						statistics.addKeyValuePair(StatisticsType.ATS_ID, oe.getAsString());
						statistics.addKeyValuePair(StatisticsType.OPERATION_NAME, oe.getOperationName());
						statistics.addKeyValuePair(StatisticsType.RUNTIME_TOTAL, timer.checkTime());
						final BenchmarkResult<?> br = new BenchmarkResult<>(Activator.PLUGIN_ID,
								"automata script interpreter benchmark results", statistics);
						mServices.getResultService().reportResult(Activator.PLUGIN_ID, br);
					}
					assert op.checkResult(new StringFactory()) : "Result of operation " + op.operationName()
							+ " is wrong (according to its checkResult method)";
					result = op.getResult();
				} catch (final AutomataLibraryException e) {
					throw new InterpreterException(oe.getLocation(), e);
				} catch (final AssertionError e) {
					throw new InterpreterException(oe.getLocation(), e);
				} catch (final OutOfMemoryError e) {
					throw new InterpreterException(oe.getLocation(), e);
				}
			}
		}
		return result;
	}
	
	private Boolean interpret(final RelationalExpressionAST re) throws InterpreterException {
		final List<AtsASTNode> children = re.getOutgoingNodes();
		if (re.getExpectingType() == Integer.class) {
			final int v1 = (Integer) interpret(children.get(0));
			final int v2 = (Integer) interpret(children.get(1));
			switch (re.getOperator()) {
				case GREATERTHAN:
					return v1 > v2;
				case LESSTHAN:
					return v1 < v2;
				case GREATER_EQ_THAN:
					return v1 >= v2;
				case LESS_EQ_THAN:
					return v1 <= v2;
				case EQ:
					return v1 == v2;
				case NOT_EQ:
					return v1 != v2;
				default:
					throw new InterpreterException(re.getLocation(), "This type of operator is not supported: "
							+ re.getOperator());
			}
		}
		return null;
	}
	
	private Object interpret(final ReturnStatementAST rst) throws InterpreterException {
		final List<AtsASTNode> children = rst.getOutgoingNodes();
		// Change the flow
		mFlow = Flow.RETURN;
		if (children.size() == 0) {
			return null;
		} else {
			return interpret(children.get(0));
		}
	}
	
	private Object interpret(final StatementListAST stmtList) throws InterpreterException {
		for (final AtsASTNode stmt : stmtList.getOutgoingNodes()) {
			interpret(stmt);
		}
		return null;
	}
	
	private Integer interpret(final UnaryExpressionAST ue) throws InterpreterException {
		final List<AtsASTNode> children = ue.getOutgoingNodes();
		
		final VariableExpressionAST var = (VariableExpressionAST) children.get(0);
		final Integer oldVal = (Integer) interpret(var);
		
		switch (ue.getOperator()) {
			case EXPR_PLUSPLUS: {
				mVariables.put(var.getIdentifier(), oldVal + 1);
				return oldVal;
			}
			case EXPR_MINUSMINUS: {
				mVariables.put(var.getIdentifier(), oldVal - 1);
				return oldVal;
			}
			case PLUSPLUS_EXPR: {
				mVariables.put(var.getIdentifier(), oldVal + 1);
				return oldVal + 1;
			}
			case MINUSMINUS_EXPR: {
				mVariables.put(var.getIdentifier(), oldVal - 1);
				return oldVal - 1;
			}
			default: {
				final String message = ue.getLocation().getStartLine()
						+ ": UnaryExpression: This type of operator is not supported: " + ue.getOperator();
				throw new InterpreterException(ue.getLocation(), message);
			}
		}
	}
	
	private Object interpret(final VariableDeclarationAST vd) throws InterpreterException {
		final List<AtsASTNode> children = vd.getOutgoingNodes();
		Object value = null;
		if (children.size() == 1) {
			value = interpret(children.get(0));
		}
		
		for (final String id : vd.getIdentifiers()) {
			if (value == null) {
				final String longDescr = "Var \"" + id + "\" is assigned \"null\".";
				throw new InterpreterException(vd.getLocation(), longDescr);
			}
			mVariables.put(id, value);
		}
		return null;
	}
	
	private Object interpret(final VariableExpressionAST v) throws InterpreterException {
		if (!mVariables.containsKey(v.getIdentifier())) {
			final String longDescr = "Variable \"" + v.getIdentifier() + "\" was not declared before.";
			throw new InterpreterException(v.getLocation(), longDescr);
		}
		return mVariables.get(v.getIdentifier());
	}
	
	private Object interpret(final WhileStatementAST ws) throws InterpreterException {
		final List<AtsASTNode> children = ws.getOutgoingNodes();
		Boolean loopCondition = (Boolean) interpret(children.get(0));
		while (loopCondition) {
			final List<AtsASTNode> statementList = children.get(1).getOutgoingNodes();
			secondLoop: for (int i = 0; i < statementList.size(); i++) {
				interpret(statementList.get(i));
				if (mFlow != Flow.NORMAL) {
					switch (mFlow) {
						case BREAK:
						case RETURN: {
							mFlow = Flow.NORMAL;
							return null;
						}
						case CONTINUE: {
							mFlow = Flow.NORMAL;
							break secondLoop;
						}
						default:
							throw new UnsupportedOperationException();
					}
				}
			}
			loopCondition = (Boolean) interpret(children.get(0));
		}
		return null;
	}
	
	/**
	 * Reports the results of assert statements to the ILogger and to Ultimate as a GenericResult.
	 * 
	 * @param errorMessage
	 */
	private void reportResult(final Finished finished, final String errorMessage) {
		mLogger.info("----------------- Test Summary -----------------");
		boolean oneOrMoreAssertionsFailed = false;
		for (final GenericResultAtElement<AtsASTNode> test : mResultOfAssertStatements) {
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, test);
			if (test.getSeverity() == Severity.ERROR) {
				oneOrMoreAssertionsFailed = true;
			}
			reportToLogger(LoggerSeverity.INFO,
					"Line " + test.getLocation().getStartLine() + ": " + test.getShortDescription());
		}
		OverallResult overallResult;
		final LoggerSeverity loggerSeverity;
		if (finished == Finished.FINISHED) {
			loggerSeverity = LoggerSeverity.INFO;
			if (mResultOfAssertStatements.isEmpty()) {
				overallResult = OverallResult.NO_ASSERTION;
			} else if (oneOrMoreAssertionsFailed) {
				overallResult = OverallResult.SOME_ASSERTION_FAILED;
			} else {
				overallResult = OverallResult.ALL_ASSERTIONS_HOLD;
			}
		} else if (finished == Finished.TIMEOUT) {
			loggerSeverity = LoggerSeverity.INFO;
			overallResult = OverallResult.TIMEOUT;
		} else if (finished == Finished.OUTOFMEMORY) {
			loggerSeverity = LoggerSeverity.INFO;
			overallResult = OverallResult.OUT_OF_MEMORY;
		} else if (finished == Finished.ERROR) {
			loggerSeverity = LoggerSeverity.ERROR;
			overallResult = OverallResult.EXCEPTION_OR_ERROR;
		} else {
			throw new AssertionError();
		}
		final IResult result =
				new AutomataScriptInterpreterOverallResult(Activator.PLUGIN_ID, overallResult, errorMessage);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		reportToLogger(loggerSeverity, result.getLongDescription());
	}
	
	@Override
	public void printMessage(final Severity severityForResult, final LoggerSeverity severityForLogger,
			final String longDescr,
			final String shortDescr, final AtsASTNode node) {
		reportToUltimate(severityForResult, longDescr, shortDescr, node);
		reportToLogger(severityForLogger, longDescr);
	}
	
	/**
	 * Reports the given string with the given severity to Ultimate as a GenericResult
	 * 
	 * @param sev
	 *            the severity
	 * @param longDescr
	 *            the string to be reported
	 * @param node
	 *            AtsASTNode for which this String is reported
	 */
	private void reportToUltimate(final Severity sev, final String longDescr, final String shortDescr,
			final AtsASTNode node) {
		IResult result;
		if (node == null) {
			result = new GenericResult(Activator.PLUGIN_ID, shortDescr, longDescr, sev);
		} else {
			result = new GenericResultAtElement<AtsASTNode>(node, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), shortDescr, longDescr, sev);
		}
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}
	
	/**
	 * Reports the given string with the given severity to the logger
	 * 
	 * @param sev
	 *            the severity of the string
	 * @param toPrint
	 *            the string to be printed
	 */
	private void reportToLogger(final LoggerSeverity sev, final String toPrint) {
		switch (sev) {
			case ERROR:
				mLogger.error(toPrint);
				break;
			case INFO:
				mLogger.info(toPrint);
				break;
			case WARNING:
				mLogger.warn(toPrint);
				break;
			case DEBUG:
				mLogger.debug(toPrint);
				break;
			default:
				mLogger.info(toPrint);
		}
	}
	
	/**
	 * Gets an object of an automata operation indicated by OperationInvocationExpression, if the operation exists and
	 * all arguments have correct type. Otherwise it returns null.
	 * 
	 * @param oe
	 *            the automata operation
	 * @param arguments
	 *            the given arguments for this operation
	 * @return an object of the automata operation or null
	 * @throws InterpreterException
	 *             if there couldn't construct an object of the operation
	 * @throws UnsupportedOperationException
	 *             if the operation does not exist
	 */
	
	@SuppressWarnings("unchecked")
	private IOperation<String, String> getAutomataOperation(final OperationInvocationExpressionAST oe,
			final ArrayList<Object> arguments) throws InterpreterException {
		final String operationName = oe.getOperationName().toLowerCase();
		IOperation<String, String> result = null;
		if (mExistingOperations.containsKey(operationName)) {
			final Set<Class<?>> operationClasses = mExistingOperations.get(operationName);
			for (final Class<?> operationClass : operationClasses) {
				final Constructor<?>[] operationConstructors = operationClass.getConstructors();
				if (operationConstructors.length == 0) {
					final String description = "Error in automata library: operation " + operationName
							+ " does not have a constructor";
					throw new InterpreterException(oe.getLocation(), description, description);
				}
				// Find the constructor which expects the correct arguments
				for (final Constructor<?> c : operationConstructors) {
					// Convention: If the first parameter is a StateFactory, we
					// prepend a StringFactory to the arguments.
					final Object[] augmentedArgs = prependStateFactoryIfNecessary(c, arguments);
					final Object[] argumentsWithServices = prependAutomataLibraryServicesIfNecessary(c, augmentedArgs);
					if (allArgumentsHaveCorrectTypeForThisConstructor(c, argumentsWithServices)) {
						try {
							result = (IOperation<String, String>) c.newInstance(argumentsWithServices);
							return result;
						} catch (final InstantiationException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (final IllegalAccessException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (final InvocationTargetException e) {
							final Throwable targetException = e.getTargetException();
							if (targetException instanceof InterpreterException) {
								throw (InterpreterException) targetException;
							} else {
								throw new InterpreterException(oe.getLocation(), targetException);
							}
						} catch (final OutOfMemoryError e) {
							throw new InterpreterException(oe.getLocation(), e);
						}
					}
				}
			}
		} else {
			final String allOperations = (new ListExistingOperations(mExistingOperations)).prettyPrint();
			final String longDescr =
					"Unsupported operation \"" + operationName + "\"" + System.getProperty("line.separator")
							+ "We support only the following operations " + System.getProperty("line.separator")
							+ allOperations;
			throw new InterpreterException(oe.getLocation(), longDescr);
		}
		assert (result == null);
		{
			final String shortDescr = "Operation error";
			String longDescr = "Operation \"" + oe.getOperationName() + "\" is not defined for "
					+ (arguments.size() == 1 ? "this type of argument." : "these types of arguments.");
			longDescr += " (";
			for (final Object argument : arguments) {
				longDescr += argument.getClass().getSimpleName() + " ";
			}
			longDescr += ")";
			printMessage(Severity.ERROR, LoggerSeverity.DEBUG, longDescr, shortDescr, oe);
			throw new InterpreterException(oe.getLocation(), longDescr);
		}
	}
	
	/**
	 * Prepend mServices to args if AutomataLibraryServices is the first parameter of the constructor. FIXME: This is
	 * only a workaround! In the future AutomataLibraryServices will be the first argument of each IOperation and we
	 * will always prepend mServices
	 */
	private Object[] prependAutomataLibraryServicesIfNecessary(final Constructor<?> c, final Object[] args) {
		boolean firstParameterIsAutomataLibraryServices;
		final Class<?> fstParam = c.getParameterTypes()[0];
		if (AutomataLibraryServices.class.isAssignableFrom(fstParam)) {
			firstParameterIsAutomataLibraryServices = true;
		} else {
			firstParameterIsAutomataLibraryServices = false;
		}
		Object[] result;
		if (firstParameterIsAutomataLibraryServices) {
			final List<Object> list = new ArrayList<>();
			list.add(new AutomataLibraryServices(mServices));
			list.addAll(Arrays.asList(args));
			result = list.toArray();
		} else {
			result = args;
		}
		return result;
	}
	
	/**
	 * Return args.toArray(), but prepend a new StringFactory if the first parameter of the Constructor c is a
	 * StateFacotry.
	 */
	private Object[] prependStateFactoryIfNecessary(final Constructor<?> c, final List<Object> args) {
		boolean firstParameterIsStateFactory;
		final Class<?> fstParam = c.getParameterTypes()[0];
		if (IStateFactory.class.isAssignableFrom(fstParam)) {
			firstParameterIsStateFactory = true;
		} else {
			firstParameterIsStateFactory = false;
		}
		boolean firstParameterIsServicesAndSecondParameterIsStateFactory;
		firstParameterIsServicesAndSecondParameterIsStateFactory =
				firstParameterIsServicesAndSecondParameterIsStateFactory(
						c, fstParam);
		Object result[];
		if (firstParameterIsStateFactory || firstParameterIsServicesAndSecondParameterIsStateFactory) {
			result = new Object[args.size() + 1];
			result[0] = new StringFactory();
			int offset = 1;
			for (final Object arg : args) {
				result[offset] = arg;
				offset++;
			}
		} else {
			result = args.toArray();
		}
		return result;
	}
	
	/**
	 * TODO: get rid of this workaround Workaround that is necessary as long as not all operations use Services as their
	 * first parameter.
	 */
	private boolean firstParameterIsServicesAndSecondParameterIsStateFactory(final Constructor<?> c,
			final Class<?> fstParam) {
		boolean firstParameterIsServicesAndSecondParameterIsStateFactory;
		if (c.getParameterTypes().length < 2) {
			firstParameterIsServicesAndSecondParameterIsStateFactory = false;
		} else {
			final Class<?> sndParam = c.getParameterTypes()[1];
			if (AutomataLibraryServices.class.isAssignableFrom(fstParam)) {
				if (IStateFactory.class.isAssignableFrom(sndParam)) {
					firstParameterIsServicesAndSecondParameterIsStateFactory = true;
				} else {
					firstParameterIsServicesAndSecondParameterIsStateFactory = false;
				}
			} else {
				firstParameterIsServicesAndSecondParameterIsStateFactory = false;
			}
		}
		return firstParameterIsServicesAndSecondParameterIsStateFactory;
	}
	
	/**
	 * Checks if all arguments have the correct type.
	 * 
	 * @param c
	 *            The constructor of the operation class.
	 * @param arguments
	 *            The arguments to check
	 * @return true if and only if all arguments have the correct type. Otherwise false.
	 */
	private boolean allArgumentsHaveCorrectTypeForThisConstructor(final Constructor<?> c, final Object[] arguments) {
		if (arguments.length == c.getParameterTypes().length) {
			int i = 0;
			for (final Class<?> type : c.getParameterTypes()) {
				if (AssignableTest.isAssignableFrom(type, arguments[i].getClass())) {
					i++;
				} else {
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Finds all automata operations implementing the IOperation interface. It maps the operation names to set of class
	 * objects, because there may exist different classes for the same operation. E.g. accepts-operation for
	 * NestedWordAutomata and accepts-operations for PetriNets
	 * 
	 * @return A map from class names to set of class objects from classes found in the directories.
	 */
	private Map<String, Set<Class<?>>> getOperationClasses() {
		final Map<String, Set<Class<?>>> result = new HashMap<String, Set<Class<?>>>();
		/*
		 * NOTE: The following directories are scanned recursively. Hence, do not add directories where one directory is
		 * a subdirectory of another in the list to avoid unnecessary work.
		 */
		final String[] packages = {
				"de.uni_freiburg.informatik.ultimate.automata.alternating",
				"de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi",
				"de.uni_freiburg.informatik.ultimate.automata.nestedword.operations",
				"de.uni_freiburg.informatik.ultimate.automata.petrinet",
				"de.uni_freiburg.informatik.ultimate.automata.tree.operations"
		};
		for (final String packageName : packages) {
			final Collection<File> files = filesInDirectory(getPathFromPackageName(packageName));
			
			for (final File file : files) {
				final String filename = file.getName();
				if (filename.endsWith(".class")) {
					final Class<?> clazz = getClassFromFile(packageName, file);
					if (clazz != null && classImplementsIOperationInterface(clazz)) {
						tryAdd(result, clazz);
						continue;
					}
				}
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Not considering " + file.getAbsolutePath());
				}
			}
		}
		return result;
	}
	
	private Class<?> getClassFromFile(final String packageName, final File file) {
		final String qualifiedName = getQualifiedNameFromFile(packageName, file);
		final Class<?> clazz;
		try {
			clazz = Class.forName(qualifiedName);
		} catch (final ClassNotFoundException e) {
			mLogger.error("Couldn't load/find class " + qualifiedName);
			throw new RuntimeException(e);
		}
		return clazz;
	}
	
	private boolean tryAdd(final Map<String, Set<Class<?>>> result, final Class<?> clazz) {
		final String opName = clazz.getSimpleName().toLowerCase();
		Set<Class<?>> set = result.get(opName);
		if (set == null) {
			set = new HashSet<>();
			result.put(opName, set);
		}
		set.add(clazz);
		return true;
	}
	
	/**
	 * Tries to resolve the fully qualified name from the package name and the found file.
	 * If the package is a.b.c.d and we found a class with the path /foo/bar/a/b/c/d/huh/OurClass.class, then the fully
	 * qualified name is a.b.c.d.huh.OurClass
	 * 
	 * @param packageName
	 * @param file
	 * @return
	 */
	private String getQualifiedNameFromFile(final String packageName, final File file) {
		assert file != null;
		assert file.getName().endsWith(".class");
		
		final String fullname = file.getAbsolutePath();
		final String filenameWithoutSuffix = fullname.substring(0, fullname.length() - 6);
		final String knownPath = getPathFromPackageName(packageName);
		final int validAfter = filenameWithoutSuffix.indexOf(knownPath);
		assert validAfter != -1;
		
		return filenameWithoutSuffix.substring(validAfter).replace(File.separatorChar, '.');
	}
	
	private String getPathFromPackageName(final String packageName) {
		return packageName.replace(".", File.separator);
	}
	
	/**
	 * Checks if the given class object implements the IOperation interface.
	 * 
	 * @param c
	 *            the class object to check
	 * @return true if and only if the class object c implements the IOperation interface. Otherwise false.
	 */
	private static boolean classImplementsIOperationInterface(final Class<?> c) {
		final Class<?>[] implementedInterfaces = c.getInterfaces();
		for (final Class<?> interFace : implementedInterfaces) {
			if (interFace.equals(IOperation.class)) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Return the filenames of the files in the given directory. We use the classloader to get the URL of this folder.
	 * We support only URLs with protocol <i>file</i> and <i>bundleresource</i>. At the moment these are the only ones
	 * that occur in Website and WebsiteEclipseBridge.
	 */
	private Collection<File> filesInDirectory(final String dir) {
		final URL dirURL = IOperation.class.getClassLoader().getResource(dir);
		if (dirURL == null) {
			mLogger.error("Directory \"" + dir + "\" does not exist");
			return Collections.emptyList();
		}
		final String protocol = dirURL.getProtocol();
		final File dirFile;
		if (protocol.equals("file")) {
			try {
				dirFile = new File(dirURL.toURI());
			} catch (final URISyntaxException e) {
				mLogger.error("Directory \"" + dir + "\" does not exist");
				return Collections.emptyList();
			}
		} else if (protocol.equals("bundleresource")) {
			try {
				final URL fileURL = FileLocator.toFileURL(dirURL);
				dirFile = new File(fileURL.getFile());
			} catch (final Exception e) {
				mLogger.error("Directory \"" + dir + "\" does not exist");
				return Collections.emptyList();
			}
		} else {
			throw new UnsupportedOperationException("unknown protocol");
		}
		return resolveDirectories(Arrays.asList(dirFile));
	}
	
	private Collection<File> resolveDirectories(final Collection<File> files) {
		final ArrayDeque<File> worklist = new ArrayDeque<File>();
		final ArrayList<File> rtr = new ArrayList<File>();
		worklist.addAll(files);
		while (!worklist.isEmpty()) {
			final File file = worklist.removeFirst();
			if (file.isFile()) {
				rtr.add(file);
				continue;
			}
			worklist.addAll(Arrays.asList(file.listFiles()));
		}
		return rtr;
	}
	
	/**
	 * Exception that is thrown if the interpreter has found an error in the ats file. The short description may be null
	 * which means that no short description is provided.
	 */
	private static class InterpreterException extends Exception {
		private static final long serialVersionUID = -7514869048479460179L;
		private final ILocation mLocation;
		private final String mShortDescription;
		private final String mLongDescription;
		
		public InterpreterException(final ILocation location, final String longDescription) {
			super();
			mLocation = location;
			mLongDescription = longDescription;
			mShortDescription = null;
		}
		
		public InterpreterException(final ILocation location, final String longDescription,
				final String shortDescription) {
			super();
			mLocation = location;
			mLongDescription = longDescription;
			mShortDescription = shortDescription;
		}
		
		public InterpreterException(final ILocation location, final Throwable cause) {
			// pass throwable as cause to superclass
			super(cause);
			mLocation = location;
			mLongDescription = generateLongDescriptionFromThrowable(cause);
			mShortDescription = cause.getClass().getSimpleName();
		}
		
		private String generateLongDescriptionFromThrowable(final Throwable throwable) {
			if (throwable.getMessage() == null) {
				return throwable.getClass().getSimpleName();
			} else {
				return throwable.getClass().getSimpleName() + ": " + throwable.getMessage();
			}
		}
		
		public ILocation getLocation() {
			return mLocation;
		}
		
		public String getLongDescription() {
			return mLongDescription;
		}
		
		public String getShortDescription() {
			return mShortDescription;
		}
	}
	
	public static class SimpleTimer {
		long mStartTime;
		
		public SimpleTimer() {
			mStartTime = System.nanoTime();
		}
		
		public long checkTime() {
			return System.nanoTime() - mStartTime;
		}
	}
}
