/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.Reader;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
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
import java.util.ListIterator;
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
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AutomataScriptInterpreterOverallResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AutomataScriptInterpreterOverallResult.OverallResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AutomataScriptParserRun;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AssignmentExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitionsAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BinaryExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BreakStatementAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanExpressionAST;
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
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TreeAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.UnaryExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableDeclarationAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableExpressionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.WhileStatementAST;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 * This is the main class for interpreting automata script test files. It fulfills the following tasks: - Interpreting
 * automata definitions - Type checking the automata script test file - Interpreting the automata script test file -
 * Generation and output of the results
 *
 * @author musab@informatik.uni-freiburg.de
 */
public class TestFileInterpreter implements IMessagePrinter {
	private static final boolean PRINT_STACK_TRACE_FOR_EXCEPTIONS = true;

	public static final String WRITE = "write";
	public static final String PRINT = "print";
	public static final String ASSERT = "assert";
	private static final int WRITE_ARGUMENTS = 3;

	private static final String ASSERTION_HOLDS_MESSAGE = "Assertion holds.";
	private static final String ASSERTION_VIOLATED_MESSAGE = "Assertion violated!";

	private static final String ERROR_STRING = "Error: ";
	private static final String DOES_NOT_EXIST = "\" does not exist";
	private static final String DIRECTORY = "Directory \"";

	/**
	 * This enum represents the current flow of the program. It could have the values "NORMAL", "BREAK", "CONTINUE", and
	 * "RETURN". It is necessary to implement the "continue" and "break" function for loops.
	 *
	 * @author musab@informatik.uni-freiburg.de
	 */
	enum Flow {
		NORMAL, BREAK, CONTINUE, RETURN;
	}

	/**
	 * Logger severity.
	 *
	 * @author musab@informatik.uni-freiburg.de
	 */
	public enum LoggerSeverity {
		INFO, WARNING, ERROR, DEBUG
	}

	/**
	 * Status how a test case interpretation may have terminated.
	 *
	 * @author musab@informatik.uni-freiburg.de
	 */
	private enum Finished {
		FINISHED, TIMEOUT, ERROR, OUTOFMEMORY
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
	private final ILogger mLogger;
	/**
	 * The automaton, which was lastly printed by a print operation.
	 */
	private IAutomaton<String, String> mLastPrintedAutomaton;
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
	/**
	 * If an error occurred during the interpretation this is set to true and further interpretation is aborted.
	 */
	private final List<GenericResultAtElement<AtsASTNode>> mResultOfAssertStatements;
	private final IUltimateServiceProvider mServices;
	private final boolean mProvideStatisticsResults = true;

	/**
	 * @param services
	 *            Ultimate services.
	 */
	public TestFileInterpreter(final IUltimateServiceProvider services) {
		assert services != null;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		readPreferences();
		assert isStatisticsEnumAlphabeticallySorted() : "The entries of enum StatisticsType must be sorted alphabetically.";
		mVariables = new HashMap<>();
		mFlow = Flow.NORMAL;
		mAutomataInterpreter = new AutomataDefinitionInterpreter(this, mLogger, mServices);
		mExistingOperations = getOperationClasses();
		mLastPrintedAutomaton = null;
		mResultOfAssertStatements = new ArrayList<>();
		if (mPrintAutomataToFile) {
			final String path = mPath + File.separator + "automatascriptOutput" + getDateTime() + ".ats";
			final File file = new File(path);
			try (FileWriter writer = new FileWriter(file)) {
				mPrintWriter = new PrintWriter(writer);
			} catch (final IOException e) {
				throw new AssertionError(e);
			}
		}
	}

	private void readPreferences() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mPrintAutomataToFile = prefs.getBoolean(PreferenceInitializer.NAME_WRITE_TO_FILE);
		mPath = prefs.getString(PreferenceInitializer.NAME_PATH);
		mIgnoreOperationsAndExecuteCommandInstead = prefs.getBoolean(PreferenceInitializer.NAME_EXECUTE_COMMAND_FLAG);
		mCommandToExecute = prefs.getString(PreferenceInitializer.NAME_EXECUTE_COMMAND_STRING);
	}

	private static String getDateTime() {
		final DateFormat dateFormat = new SimpleDateFormat("yyyyMMddHHmmss");
		final Date date = new Date();
		return dateFormat.format(date);
	}

	/**
	 * Method to interpret an automatascript test file. The interpretation involves 4 steps.
	 * <ol>
	 * <li>Interpret automata definitions.</li>
	 * <li>Check the automatascript test file for correct types and undeclared variables. (Type checking)</li>
	 * <li>Interpret the automatascript test file.</li>
	 * <li>Report the results to the ILogger and to the web interface.</li>
	 * </ol>
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
			errorMessage = e.getMessage();
			reportToLogger(LoggerSeverity.INFO, "Error during interpreting automata definitions.");
			reportToLogger(LoggerSeverity.INFO, ERROR_STRING + errorMessage);
			if (e instanceof InterpreterException) {
				reportToLogger(LoggerSeverity.INFO, ERROR_STRING + ((InterpreterException) e).getShortDescription());
			}
			reportToLogger(LoggerSeverity.INFO, "Interpretation of testfile cancelled.");
			reportToUltimate(Severity.ERROR, errorMessage + " Interpretation of testfile cancelled.", "Error", node);
			interpretationFinished = Finished.ERROR;
		}

		final AtsASTNode statements;
		if (mIgnoreOperationsAndExecuteCommandInstead) {
			final String commandAdapted = substituteAutomataNames(mCommandToExecute, ats.getAutomataDefinitions());
			final String fakeFilename = "mySettingsFileGivenStringDoesNotHaveFilename";
			final String fakeFileAbsolutePath = "mySettingsFileGivenStringDoesNotHaveFileAbsolutePath";
			final Reader reader = new InputStreamReader(new ByteArrayInputStream(commandAdapted.getBytes()));
			final AutomataTestFileAST astNode =
					new AutomataScriptParserRun(mServices, mLogger, reader, fakeFilename, fakeFileAbsolutePath)
							.getResult();
			statements = astNode.getStatementList();
		} else {
			statements = ats.getStatementList();
		}

		if (interpretationFinished == Finished.FINISHED) {
			// Put all defined automata into variables map
			mVariables.putAll(mAutomataInterpreter.getAutomata());
			reportToLogger(LoggerSeverity.DEBUG, "Typechecking of test file...");
			// Type checking
			try {
				new AutomataScriptTypeChecker(mExistingOperations).checkTestFile(statements, mVariables);
			} catch (final InterpreterException e) {
				reportToLogger(LoggerSeverity.INFO, ERROR_STRING + e.getMessage());
				reportToLogger(LoggerSeverity.INFO, ERROR_STRING + e.getShortDescription());
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
			if (statements != null) {
				try {
					result = interpret(statements);
				} catch (final InterpreterException e) {
					final Throwable cause = e.getCause();
					if (cause != null) {
						if (cause instanceof AutomataOperationCanceledException) {
							interpretationFinished = Finished.TIMEOUT;
							errorMessage =
									"Timeout " + ((AutomataOperationCanceledException) cause).printRunningTaskMessage();
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
	 * Replaces <tt>$i</tt> by the <tt>i</tt>th automaton name (e.g., <tt>$5</tt> by the fifth automaton name).
	 *
	 * @param command
	 *            input command containing placeholders
	 * @param automataDefinitions
	 *            all automata found
	 * @return command with placeholders replaced by respective automaton name
	 */
	private static String substituteAutomataNames(final String command,
			final AutomataDefinitionsAST automataDefinitions) {
		String result = command;
		final List<AutomatonAST> automata = automataDefinitions.getListOfAutomataDefinitions();
		int i = automata.size();
		final ListIterator<AutomatonAST> reverseIt = automata.listIterator(i);
		while (reverseIt.hasPrevious()) {
			final AutomatonAST automatonAst = reverseIt.previous();
			final String oldName = "\\$" + i;
			final String newName = automatonAst.getName();
			result = result.replaceAll(oldName, newName);
			--i;
		}
		if (result.contains("$")) {
			final String message = "The command contained an illegal automaton reference.";
			final int size = automata.size();
			if (size == 0) {
				throw new IllegalArgumentException(message + " There were no automata found in the input.");
			} else if (size == 1) {
				throw new IllegalArgumentException(message + " There was only 1 automaton found, so only $1 is legal.");
			} else {
				throw new IllegalArgumentException(String.format(
						"%s There were only %d automata found, so only $1 to $%d are legal.", message, size, size));
			}
		}
		return result;
	}

	/**
	 * @return The automaton that was printed last by a print-operation.
	 */
	public IAutomaton<String, String> getLastPrintedAutomaton() {
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
		final Object newValue = interpret(children.get(1));

		if (newValue == null) {
			final String longDescr = "Var \"" + var.getIdentifier() + "\" is assigned \"null\".";
			throw new InterpreterException(as.getLocation(), longDescr);
		}

		final Object oldValue = mVariables.get(var.getIdentifier());
		final Integer assignValue;
		switch (as.getOperator()) {
		case ASSIGN:
			mVariables.put(var.getIdentifier(), newValue);
			break;
		case PLUSASSIGN:
			assignValue = (Integer) oldValue + (Integer) newValue;
			mVariables.put(var.getIdentifier(), assignValue);
			break;
		case MINUSASSIGN:
			assignValue = (Integer) oldValue - (Integer) newValue;
			mVariables.put(var.getIdentifier(), assignValue);
			break;
		case MULTASSIGN:
			assignValue = (Integer) oldValue * (Integer) newValue;
			mVariables.put(var.getIdentifier(), assignValue);
			break;
		case DIVASSIGN:
			assignValue = (Integer) oldValue / (Integer) newValue;
			mVariables.put(var.getIdentifier(), assignValue);
			break;
		default:
			throw new InterpreterException(as.getLocation(),
					"AssignmentExpression: This type of operator is not supported: " + as.getOperator());
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
		} else if (node instanceof TreeAST) {
			result = interpret((TreeAST) node);
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
		case AND:
			return !(Boolean) interpret(children.get(0)) ? false : (Boolean) interpret(children.get(1));
		case OR:
			return (Boolean) interpret(children.get(0)) ? true : (Boolean) interpret(children.get(1));
		default:
			final String message =
					"ConditionalBooleanExpression: This type of operator is not supported: " + cbe.getOperator();
			throw new InterpreterException(cbe.getLocation(), message);
		}
	}

	private static Object interpret(final ConstantExpressionAST ce) {
		return ce.getValue();
	}

	private Object interpret(final ContinueStatementAST cst) {
		// Change the flow
		mFlow = Flow.CONTINUE;
		return null;
	}

	private Object interpret(final ForStatementAST fs) throws InterpreterException {
		final List<AtsASTNode> children = fs.getOutgoingNodes();

		// If the loop condition is missing, we just execute the loop forever
		final boolean loopForever = children.get(0) == null;
		// execute the initialization statement, if one is existing
		if (children.get(1) != null) {
			interpret(children.get(1));
		}
		while (loopForever || (Boolean) interpret(children.get(0))) {
			final List<AtsASTNode> statementList = children.get(3).getOutgoingNodes();
			for (int i = 0; i < statementList.size(); i++) {
				interpret(statementList.get(i));
				if (mFlow == Flow.NORMAL) {
					continue;
				}
				switch (mFlow) {
				case BREAK:
				case RETURN:
					mFlow = Flow.NORMAL;
					return null;
				case CONTINUE:
					mFlow = Flow.NORMAL;
					break;
				default:
					throw new UnsupportedOperationException();
				}
			}
			// execute the update statement
			if (children.get(2) != null) {
				interpret(children.get(2));
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

	private static NestedWord<String> interpret(final NestedwordAST nw) {
		return new NestedWord<>(nw.getWordSymbols(), nw.getNestingRelation());
	}

	private static NestedLassoWord<String> interpret(final NestedLassowordAST nw) {
		final NestedWord<String> stem = interpret(nw.getStem());
		final NestedWord<String> loop = interpret(nw.getLoop());
		return new NestedLassoWord<>(stem, loop);
	}

	private static Tree<StringRankedLetter> interpret(final TreeAST t) {
		return t.getTree();
	}

	private Object interpret(final OperationInvocationExpressionAST oe) throws InterpreterException {
		final List<AtsASTNode> children = oe.getOutgoingNodes();
		if (children.size() != 1) {
			final String message =
					"OperationExpression should have only 1 child (ArgumentList). Num of children: " + children.size();
			throw new InterpreterException(oe.getLocation(), message);
		}
		if (children.get(0) == null) {
			final String message = "OperationExpression's child should not be null.";
			throw new InterpreterException(oe.getLocation(), message);
		}
		final List<AtsASTNode> argsToInterpret = children.get(0).getOutgoingNodes();
		final ArrayList<Object> arguments = new ArrayList<>(argsToInterpret.size());
		// Interpret the arguments of this operation
		for (final AtsASTNode node : argsToInterpret) {
			arguments.add(interpret(node));
		}

		Object result = null;
		if (oe.getOperationName().equalsIgnoreCase(ASSERT) && arguments.size() == 1) {
			result = executeAssertMethod(oe, arguments);
		} else if (oe.getOperationName().equalsIgnoreCase(PRINT)) {
			executePrintMethod(oe, children, arguments);
		} else if (oe.getOperationName().equalsIgnoreCase(WRITE)) {
			executeWriteMethod(oe, children, arguments);
		} else {
			result = executeLibraryMethod(oe, arguments, result);
		}
		return result;
	}

	private Object executeLibraryMethod(final OperationInvocationExpressionAST oe, final ArrayList<Object> arguments,
			final Object result) throws InterpreterException {
		final SimpleTimer timer = new SimpleTimer();
		IOperation<String, String, ? super StringFactory> op = null;
		try {
			op = getAutomataOperation(oe, arguments);
		} finally {
			if (mProvideStatisticsResults) {
				mLogger.info("reporting benchmark results");
				AutomataOperationStatistics statistics;
				if (op == null) {
					statistics = new AutomataOperationStatistics();
				} else {
					statistics = op.getAutomataOperationStatistics();
					if (statistics == null) {
						statistics = new AutomataOperationStatistics();
					}
				}
				statistics.addKeyValuePair(StatisticsType.ATS_ID, oe.getAsString());
				statistics.addKeyValuePair(StatisticsType.OPERATION_NAME, oe.getOperationName());
				statistics.addKeyValuePair(StatisticsType.RUNTIME_TOTAL_MS, timer.checkTime() / 1_000_000);
				final StatisticsResult<?> br = new StatisticsResult<>(Activator.PLUGIN_ID,
						"automata script interpreter benchmark results", statistics);
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, br);
			}
		}
		if (op != null) {
			try {
				assert op.checkResult(new StringFactory()) : "Result of operation " + op.getOperationName()
						+ " is wrong (according to its checkResult method)";
				return op.getResult();
			} catch (final AutomataLibraryException | AssertionError | OutOfMemoryError e) {
				throw new InterpreterException(oe.getLocation(), e);
			}
		}
		return result;
	}

	private void executeWriteMethod(final OperationInvocationExpressionAST oe, final List<AtsASTNode> children,
			final ArrayList<Object> arguments) throws InterpreterException {
		if (arguments.size() != WRITE_ARGUMENTS) {
			throw new InterpreterException(oe.getLocation(), "write needs three arguments");
		}
		final String filename = (String) arguments.get(1);
		final Format format;
		final String formatAsString = (String) arguments.get(2);
		try {
			format = Format.valueOf(formatAsString);
		} catch (final Exception e) {
			throw new InterpreterException(oe.getLocation(), "unknown format " + filename);
		}
		final String argsAsString = children.get(0).getAsString();
		reportToLogger(LoggerSeverity.INFO,
				"Writing " + argsAsString + " to file " + filename + " in " + format + " format.");
		final IAutomaton<String, String> automaton = (IAutomaton<String, String>) arguments.get(0);
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices), "ats", filename, format,
				"output according to \"write\" command", automaton);
	}

	private void executePrintMethod(final OperationInvocationExpressionAST oe, final List<AtsASTNode> children,
			final ArrayList<Object> arguments) throws InterpreterException {
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
						throw new InterpreterException(oe.getLocation(), "unknown format " + (String) arguments.get(1));
					}
				} else {
					throw new InterpreterException(oe.getLocation(), "if first argument of print command is an "
							+ "automaton second argument has to be a string " + "that defines an output format");
				}
			} else {
				throw new InterpreterException(oe.getLocation(),
						"if first argument of print command is an " + "automaton only two arguments are allowed");
			}
			mLastPrintedAutomaton = (IAutomaton<String, String>) arguments.get(0);
			text = new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices), "automaton",
					format, mLastPrintedAutomaton).getDefinitionAsString();
		} else {
			if (arguments.size() > 1) {
				throw new InterpreterException(oe.getLocation(),
						"if first argument of print command is not an " + "automaton no second argument allowed");
			}
			text = String.valueOf(arguments.get(0));
		}
		printMessage(Severity.INFO, LoggerSeverity.INFO, text, oe.getAsString(), oe);
		if (mPrintAutomataToFile) {
			final String comment = "/* " + oe.getAsString() + " */";
			mPrintWriter.println(comment);
			mPrintWriter.println(text);
		}
	}

	private Object executeAssertMethod(final OperationInvocationExpressionAST oe, final ArrayList<Object> arguments)
			throws AssertionError {
		Object result;
		result = arguments.get(0);
		if (result instanceof Boolean) {
			if ((Boolean) result) {
				mResultOfAssertStatements.add(new GenericResultAtElement<AtsASTNode>(oe, Activator.PLUGIN_ID,
						mServices.getBacktranslationService(), ASSERTION_HOLDS_MESSAGE, oe.getAsString(),
						Severity.INFO));
			} else {
				mResultOfAssertStatements.add(new GenericResultAtElement<AtsASTNode>(oe, Activator.PLUGIN_ID,
						mServices.getBacktranslationService(), ASSERTION_VIOLATED_MESSAGE, oe.getAsString(),
						Severity.ERROR));
			}
		} else {
			throw new AssertionError("assert expects boolean result, type checker should have found this");
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
				throw new InterpreterException(re.getLocation(),
						"This type of operator is not supported: " + re.getOperator());
			}
		}
		return null;
	}

	private Object interpret(final ReturnStatementAST rst) throws InterpreterException {
		final List<AtsASTNode> children = rst.getOutgoingNodes();
		// Change the flow
		mFlow = Flow.RETURN;
		if (children.isEmpty()) {
			return null;
		}
		return interpret(children.get(0));
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
		case EXPR_PLUSPLUS:
			mVariables.put(var.getIdentifier(), oldVal + 1);
			return oldVal;
		case EXPR_MINUSMINUS:
			mVariables.put(var.getIdentifier(), oldVal - 1);
			return oldVal;
		case PLUSPLUS_EXPR:
			mVariables.put(var.getIdentifier(), oldVal + 1);
			return oldVal + 1;
		case MINUSMINUS_EXPR:
			mVariables.put(var.getIdentifier(), oldVal - 1);
			return oldVal - 1;
		default:
			final String message = ue.getLocation().getStartLine()
					+ ": UnaryExpression: This type of operator is not supported: " + ue.getOperator();
			throw new InterpreterException(ue.getLocation(), message);
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
			for (int i = 0; i < statementList.size(); i++) {
				interpret(statementList.get(i));
				if (mFlow == Flow.NORMAL) {
					continue;
				}
				switch (mFlow) {
				case BREAK:
				case RETURN:
					mFlow = Flow.NORMAL;
					return null;
				case CONTINUE:
					mFlow = Flow.NORMAL;
					break;
				default:
					throw new UnsupportedOperationException();
				}
			}
			loopCondition = (Boolean) interpret(children.get(0));
		}
		return null;
	}

	/**
	 * Reports the results of assert statements to the ILogger and to Ultimate as a GenericResult.
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
			final String longDescr, final String shortDescr, final AtsASTNode node) {
		reportToUltimate(severityForResult, longDescr, shortDescr, node);
		reportToLogger(severityForLogger, longDescr);
	}

	/**
	 * Reports the given string with the given severity to Ultimate as a GenericResult.
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
			result = new GenericResultAtElement<>(node, Activator.PLUGIN_ID, mServices.getBacktranslationService(),
					shortDescr, longDescr, sev);
		}
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

	/**
	 * Reports the given string with the given severity to the logger.
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
		case WARNING:
			mLogger.warn(toPrint);
			break;
		case DEBUG:
			mLogger.debug(toPrint);
			break;
		case INFO:
		default:
			mLogger.info(toPrint);
			break;
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
	private IOperation<String, String, ? super StringFactory> getAutomataOperation(
			final OperationInvocationExpressionAST oe, final List<Object> arguments) throws InterpreterException {
		final String operationName = oe.getOperationName();
		if (!mExistingOperations.containsKey(operationName)) {
			final String allOperations = new ListExistingOperations(mExistingOperations).prettyPrint();
			final String longDescr = "Unsupported operation \"" + operationName + "\""
					+ System.getProperty("line.separator") + "We support only the following operations "
					+ System.getProperty("line.separator") + allOperations;
			throw new InterpreterException(oe.getLocation(), longDescr);
		}
		for (final Class<?> operationClass : mExistingOperations.get(operationName)) {
			final Constructor<?>[] operationConstructors = operationClass.getConstructors();
			if (operationConstructors.length == 0) {
				final String description =
						"Error in automata library: operation " + operationName + " does not have a constructor";
				throw new InterpreterException(oe.getLocation(), description, description);
			}
			// Find the constructor which expects the correct arguments
			for (final Constructor<?> c : operationConstructors) {
				// Convention: If the first parameter is a StateFactory, we
				// prepend a StringFactory to the arguments.
				assert isNoStateFactoryAfterSecondArgument(c.getParameterTypes()) : "constructor of "
						+ c.getDeclaringClass().getSimpleName()
						+ " violates \"services and state factory first\" convention";
				final Object[] argumentsWithServices =
						prependAutomataLibraryServicesAndStateFactoryIfNeeded(c, arguments);
				if (!allArgumentsHaveCorrectTypeForThisConstructor(c, argumentsWithServices)) {
					continue;
				}
				try {
					return (IOperation<String, String, ? super StringFactory>) c.newInstance(argumentsWithServices);
				} catch (final InstantiationException | IllegalAccessException e) {
					printStackTrace(e);
					throw new AssertionError(e);
				} catch (final InvocationTargetException e) {
					final Throwable targetException = e.getTargetException();
					if (!(targetException instanceof AutomataLibraryException)) {
						printStackTrace(e);
					}
					if (targetException instanceof InterpreterException) {
						throw (InterpreterException) targetException;
					}
					throw new InterpreterException(oe.getLocation(), targetException);
				} catch (final OutOfMemoryError e) {
					throw new InterpreterException(oe.getLocation(), e);
				}
			}
		}
		final String shortDescr = "Operation error";
		final StringBuilder longDescrBuilder = new StringBuilder();
		// @formatter:off
		longDescrBuilder.append("Operation \"")
						.append(oe.getOperationName())
						.append("\" is not defined for ")
						.append(arguments.size() == 1 ? "this type of argument." : "these types of arguments.")
						.append(" (");
		// @formatter:on
		for (final Object argument : arguments) {
			// @formatter:off
			longDescrBuilder.append(argument.getClass().getSimpleName())
							.append(" ");
			// @formatter:on
		}
		longDescrBuilder.append(")");
		final String longDescr = longDescrBuilder.toString();
		printMessage(Severity.ERROR, LoggerSeverity.DEBUG, longDescr, shortDescr, oe);
		throw new InterpreterException(oe.getLocation(), longDescr);
	}

	private static void printStackTrace(final Exception e) {
		if (PRINT_STACK_TRACE_FOR_EXCEPTIONS) {
			e.printStackTrace();
		}
	}

	/**
	 * Prepend {@link AutomataLibraryServices} and possibly {@link IStateFactory} to args.
	 * <p>
	 * By convention, every operation has a first argument of type {@link AutomataLibraryServices}. If an operation has
	 * an argument of type {@link IStateFactory}, it must come second.
	 *
	 * @return fresh list of arguments with additional arguments prepended
	 */
	private Object[] prependAutomataLibraryServicesAndStateFactoryIfNeeded(final Constructor<?> c,
			final List<Object> arguments) {
		assert isServicesFirstArgument(c.getParameterTypes());
		final boolean isStateFactorySecondArgument = isStateFactorySecondArgument(c.getParameterTypes());
		final int totalNumberOfArgs = arguments.size() + (isStateFactorySecondArgument ? 2 : 1);

		final List<Object> list = new ArrayList<>(totalNumberOfArgs);
		list.add(new AutomataLibraryServices(mServices));
		if (isStateFactorySecondArgument) {
			list.add(new StringFactory());
		}
		list.addAll(arguments);
		return list.toArray();
	}

	private static boolean isServicesFirstArgument(final Class<?>[] argsClasses) {
		if (argsClasses.length < 1) {
			// no argument at all, i.e., no services
			return false;
		}
		return AutomataLibraryServices.class.isAssignableFrom(argsClasses[0]);
	}

	private static boolean isStateFactorySecondArgument(final Class<?>[] argsClasses) {
		if (argsClasses.length < 1) {
			// no argument at all, i.e., no state factory
			return false;
		}
		return IStateFactory.class.isAssignableFrom(argsClasses[1]);
	}

	private static boolean isNoStateFactoryAfterSecondArgument(final Class<?>[] argsClasses) {
		for (int i = 2; i < argsClasses.length; i++) {
			if (IStateFactory.class.isAssignableFrom(argsClasses[i])) {
				return false;
			}
		}
		return true;
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
	private static boolean allArgumentsHaveCorrectTypeForThisConstructor(final Constructor<?> c,
			final Object[] arguments) {
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
		}
		return false;
	}

	/**
	 * Finds all automata operations implementing the IOperation interface. It maps the operation names to set of class
	 * objects, because there may exist different classes for the same operation. E.g. accepts-operation for
	 * NestedWordAutomata and accepts-operations for PetriNets
	 *
	 * @return A map from class names to set of class objects from classes found in the directories.
	 */
	private Map<String, Set<Class<?>>> getOperationClasses() {
		final Map<String, Set<Class<?>>> result = new HashMap<>();
		/*
		 * NOTE: The following directories are scanned recursively. Hence, do not add directories where one directory is
		 * a subdirectory of another in the list to avoid unnecessary work.
		 */
		final String[] packages = { "de.uni_freiburg.informatik.ultimate.automata.alternating",
				"de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi",
				"de.uni_freiburg.informatik.ultimate.automata.nestedword.operations",
				"de.uni_freiburg.informatik.ultimate.automata.petrinet",
				"de.uni_freiburg.informatik.ultimate.automata.tree.operations" };
		for (final String packageName : packages) {
			final Collection<File> files = filesInDirectory(getPathFromPackageName(packageName));

			for (final File file : files) {
				final String filename = file.getName();
				final boolean wasOperation = addClassIfOperation(result, packageName, file, filename);
				if (!wasOperation && mLogger.isDebugEnabled()) {
					mLogger.debug("Not considering " + file.getAbsolutePath());
				}
			}
		}
		return result;
	}

	private boolean addClassIfOperation(final Map<String, Set<Class<?>>> result, final String packageName,
			final File file, final String filename) {
		if (!filename.endsWith(".class")) {
			return false;
		}
		final Class<?> clazz = getClassFromFile(packageName, file);
		if (clazz == null) {
			return false;
		}
		if (classIsAbstract(clazz)) {
			return false;
		}

		if (!ReflectionUtil.classImplementsInterface(clazz, IOperation.class)) {
			return false;
		}

		final String opName = IOperation.computeOperationName((Class<? extends IOperation>) clazz);
		Set<Class<?>> set = result.get(opName);
		if (set == null) {
			set = new HashSet<>();
			result.put(opName, set);
		}
		set.add(clazz);
		return true;
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

	/**
	 * Tries to resolve the fully qualified name from the package name and the found file. If the package is a.b.c.d and
	 * we found a class with the path /foo/bar/a/b/c/d/huh/OurClass.class, then the fully qualified name is
	 * a.b.c.d.huh.OurClass
	 */
	private static String getQualifiedNameFromFile(final String packageName, final File file) {
		assert file != null;
		assert file.getName().endsWith(".class");

		final String fullname = file.getAbsolutePath();
		final String filenameWithoutSuffix = fullname.substring(0, fullname.length() - 6);
		final String knownPath = getPathFromPackageName(packageName);
		final int validAfter = filenameWithoutSuffix.indexOf(knownPath);
		assert validAfter != -1;

		return filenameWithoutSuffix.substring(validAfter).replace(File.separatorChar, '.');
	}

	private static String getPathFromPackageName(final String packageName) {
		return packageName.replace(".", File.separator);
	}

	private static boolean classIsAbstract(final Class<?> clazz) {
		return Modifier.isAbstract(clazz.getModifiers());
	}

	/**
	 * Return the filenames of the files in the given directory. We use the classloader to get the URL of this folder.
	 * We support only URLs with protocol <i>file</i> and <i>bundleresource</i>. At the moment these are the only ones
	 * that occur in Website and WebsiteEclipseBridge.
	 */
	private Collection<File> filesInDirectory(final String dir) {
		final URL dirUrl = IOperation.class.getClassLoader().getResource(dir);
		if (dirUrl == null) {
			mLogger.error(DIRECTORY + dir + DOES_NOT_EXIST);
			return Collections.emptyList();
		}
		final String protocol = dirUrl.getProtocol();
		final File dirFile;
		if ("file".equals(protocol)) {
			try {
				dirFile = new File(dirUrl.toURI());
			} catch (final URISyntaxException e) {
				mLogger.error(DIRECTORY + dir + DOES_NOT_EXIST);
				return Collections.emptyList();
			}
		} else if ("bundleresource".equals(protocol)) {
			try {
				final URL fileUrl = FileLocator.toFileURL(dirUrl);
				dirFile = new File(fileUrl.getFile());
			} catch (final Exception e) {
				mLogger.error(DIRECTORY + dir + DOES_NOT_EXIST);
				return Collections.emptyList();
			}
		} else {
			throw new UnsupportedOperationException("unknown protocol");
		}
		return resolveDirectories(Arrays.asList(dirFile));
	}

	private static Collection<File> resolveDirectories(final Collection<File> files) {
		final ArrayDeque<File> worklist = new ArrayDeque<>();
		final ArrayList<File> rtr = new ArrayList<>();
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

	private static boolean isStatisticsEnumAlphabeticallySorted() {
		final StatisticsType[] values = StatisticsType.values();
		for (int i = 1; i < values.length; ++i) {
			if (values[i - 1].toString().compareTo(values[i].toString()) > 0) {
				final StatisticsType tooLate = values[i];
				final StatisticsType tooEarly = values[i - 1];
				assert false : "The entries of enum StatisticsType are not sorted alphabetically. Too late: " + tooLate
						+ " too early: " + tooEarly;
				return false;
			}
		}
		return true;
	}

	private static class SimpleTimer {
		private final long mStartTime;

		public SimpleTimer() {
			mStartTime = System.nanoTime();
		}

		/**
		 * @return Time difference of the timer between start and now.
		 */
		public long checkTime() {
			return System.nanoTime() - mStartTime;
		}
	}
}
