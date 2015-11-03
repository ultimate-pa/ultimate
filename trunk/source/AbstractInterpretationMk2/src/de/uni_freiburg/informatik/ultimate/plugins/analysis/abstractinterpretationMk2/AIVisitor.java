/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util.IRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util.IStatementVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * Used to evaluate boogie statements during abstract interpretation
 * 
 * @author Jan Hättig
 */
@SuppressWarnings("rawtypes")
public class AIVisitor implements IRCFGVisitor, IStatementVisitor {

	/**
	 * The logger object for printing
	 */
	private final Logger mLogger;
	/**
	 * The boogie symbol table mapps each variables name as string to a varable
	 * declaration
	 */
	private final BoogieSymbolTable mSymbolTable;
	/**
	 * The domain used to do the analysis. The sub type of it depends on the
	 * chosen domain
	 */
	private final IAbstractDomain mDomain;

	/**
	 * Holds the states before entering a code block. This should begin with one
	 * state. If any assume returns more than one state the states will be
	 * processed in parallel.
	 */
	private List<StackState> mCurrentStates;

	/**
	 * This state will be manipulated in a code block. This should begin with
	 * one state. If any assume returns more than one state the states will be
	 * processed in parallel.
	 * 
	 * !! Only add non-bottom states if this is am empty list, that means there
	 * have only been resulting bottom-states
	 */
	private List<StackState> mResultingStates;

	/**
	 * Holds a list with a sequence element for each sequential code block which
	 * was entered and information about whether it is executed in parallel.
	 */
	private LinkedList<AIVisitorStackElement> mCompositions;

	/**
	 * Can be set to false to interrupt processing
	 */
	private boolean mContinueProcessing;

	/**
	 * If the visitor encounters any errors (like unsupported syntax), an error
	 * message is written to this variable. The AbstractInterpreter checks for
	 * such messages and returns an appropriate result.
	 */
	private String mError = "";

	/**
	 * This will be set to true if an assert was violated TODO: is this still in
	 * use?
	 */
	private boolean mViolatedAssert;

	/**
	 * The result of the analysis
	 */
	private String mResult;

	/**
	 * Determines if the pr
	 * 
	 * @return
	 */
	public boolean getContinueProcessing() {
		return mContinueProcessing;
	}

	/**
	 * Sets the current state. The state which will be used at the beginning of
	 * the edge.
	 * 
	 * @param state
	 */
	public void setCurrentState(StackState state) {
		mCurrentStates = new ArrayList<StackState>();
		mCurrentStates.add(state);
	}

	/**
	 * @return The state resulting after visiting an edge.
	 */
	public List<StackState> getResultingStates() {
		return mResultingStates;
	}

	/**
	 * @return The error of the last analysis. If there was no error this is
	 *         null.
	 */
	public String getError() {
		return mError;
	}

	/**
	 * When an assert was violated this is set to true
	 * 
	 * @return
	 */
	public boolean violatedAssert() {
		return mViolatedAssert;
	}

	/**
	 * The result of the last analysis
	 * 
	 * @return
	 */
	public String getResult() {
		return mResult;
	}

	/**
	 * Constructor
	 * 
	 * 
	 * @param logger
	 * @param services
	 * @param symbolTable
	 * @param domain
	 * @param numbersForWidening
	 */
	public AIVisitor(Logger logger, IUltimateServiceProvider services, BoogieSymbolTable symbolTable,
			IAbstractDomain<?> domain) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mDomain = domain;
		mResult = null;
		mViolatedAssert = false;
		mContinueProcessing = true;
		mCompositions = new LinkedList<AIVisitorStackElement>();
		mCurrentStates = null;
		mResultingStates = null;
	}

	@Override
	public void visitEdge(RCFGEdge e) {
		/**
		 * After visiting each edge, the resulting state is in mMergedState
		 */
		// mLogger.debug("### Visiting: " + e.getSource() + " -> " +
		// e.getTarget());
		// mDebugOuputNesting = "";

		mContinueProcessing = true;

		mResultingStates = new ArrayList<StackState>();

		assert (mCurrentStates.size() == 1); // must start with exactly one
												// state
		mResultingStates.add(mCurrentStates.get(0).incrementTop());

		// add a root stack element
		mCompositions.clear();
		mCompositions.push(new AIVisitorStackElement(false, null));
	}

	@Override
	public void visitedEdge(RCFGEdge e) {
	}

	@Override
	public void visitCodeBlock(CodeBlock c) {
		/**
		 * After visiting each code block, the resulting state is in mResulting
		 * state It will be merged into mMergedState. So in case we are in a
		 * parallel sequence the merged state can be extracted from there
		 */
		// mLogger.debug("### CodeBlock: " + c.toString());
		// mDebugOuputNesting += " ";
		// mLogger.debug(mDebugOuputNesting + "States:\n" +
		// mResultingStates.toString());
	}

	@Override
	public void visitedCodeBlock(CodeBlock c) {
		// if processing in parallel merge the resulting
		// state into the composition
		AIVisitorStackElement seq = mCompositions.peek();
		if (seq.getProcessInParalell() && mResultingStates != null) {
			if (seq.getResultingStates() == null) {
				seq.setResultingStates(mResultingStates);
			} else {
				// merge the states, put them in one list
				seq.getResultingStates().addAll(mResultingStates);
				// seq.setResultingState(mResultingState.merge(seq.getResultingState(),
				// false));
			}
			// restore mResultingStates like before the code block was executed
			mResultingStates = new ArrayList<StackState>();
			for (StackState state : seq.getRootStates()) {
				mResultingStates.add(state.incrementTop());
			}
		}

		// mLogger.debug(mDebugOuputNesting + " States:\n" +
		// mResultingStates.toString());
		// mDebugOuputNesting = mDebugOuputNesting.substring(0,
		// mDebugOuputNesting.length() - 1);
		// mLogger.debug(mDebugOuputNesting + "< CodeBlock END");
	}

	@Override
	public void visit(ParallelComposition c) {
		/**
		 * After visiting each edge, the resulting state is in mResulting state
		 * which gets merged to mMergedState
		 */
		mCompositions.push(new AIVisitorStackElement(true, mResultingStates));

		// get a copy of mResultingStates to process the first element
		List<StackState> newResultingStates = new ArrayList<StackState>();
		for (StackState state : mResultingStates) {
			newResultingStates.add(state.incrementTop());
		}
		mResultingStates = newResultingStates;

		// mLogger.debug(mDebugOuputNesting + "> ParallelComposition START");
		// mDebugOuputNesting += " ";
		// mLogger.debug(mDebugOuputNesting + "compositions: " +
		// mCompositions.size());
	}

	@Override
	public void visited(ParallelComposition c) {
		/**
		 * After visiting each edge, the resulting state is in mResulting state
		 * which gets merged to mMergedState. Now we take that merged state, as
		 * it is the resulting state of the parallel composition
		 */
		AIVisitorStackElement seq = mCompositions.pop();
		mResultingStates = seq.getResultingStates();

		// mLogger.debug(mDebugOuputNesting + "compositions: " +
		// mCompositions.size());
		// mDebugOuputNesting = mDebugOuputNesting.substring(0,
		// mDebugOuputNesting.length() - 1);
		// mLogger.debug(mDebugOuputNesting + "< ParallelComposition END");
	}

	@Override
	public void visit(SequentialComposition c) {
		/**
		 * After visiting each edge the resulting state shall be the new actual
		 * state, which is done by the code block visiting function.
		 */
		// mLogger.debug(mDebugOuputNesting + "> SequentialComposition START");
		// mDebugOuputNesting += " ";

		mCompositions.push(new AIVisitorStackElement(false, null));

		// mLogger.debug(mDebugOuputNesting + " States:\n" +
		// mResultingStates.toString());
		// mLogger.debug(mDebugOuputNesting + "compositions: " +
		// mCompositions.size());
	}

	@Override
	public void visited(SequentialComposition c) {
		/**
		 * After visiting a sequential composition only the stack element has to
		 * be popped out.
		 */
		mCompositions.pop();

		// mLogger.debug(mDebugOuputNesting + " States:\n" +
		// mResultingStates.toString());
		// mLogger.debug(mDebugOuputNesting + "compositions: " +
		// mCompositions.size());
		// mDebugOuputNesting = mDebugOuputNesting.substring(0,
		// mDebugOuputNesting.length() - 1);
		// mLogger.debug(mDebugOuputNesting + "< SequentialComposition END");
	}

	@Override
	public void visit(RootEdge c) {
		throw new UnsupportedOperationException("This should not happen");
	}

	@Override
	public void visit(GotoEdge c) {
		// A goto edge means nothing. The state will be copied anyways
	}

	@Override
	public void visit(Call c) {
		// mLogger.debug("> CALL " + stmt.getMethodName());
	}

	@Override
	public void visited(Call c) {
		// mLogger.debug("< CALL " + stmt.getMethodName());
	}

	@Override
	public void visit(Return c) {
		// mLogger.debug("> RETURN " + c.getCallStatement().getMethodName());
	}

	@Override
	public void visited(Return c) {
		// mLogger.debug("< RETURN " + c.getCallStatement().getMethodName());
	}

	@Override
	public void visit(StatementSequence c) {
		/**
		 * A statement sequence does not need any stack information, since there
		 * is no nesting.
		 */
		// mLogger.debug(mDebugOuputNesting + "> StatementSequence START (" +
		// c.toString() + ")");
		// mDebugOuputNesting += " ";
		// mLogger.debug(mDebugOuputNesting + " States:\n" +
		// mResultingStates.toString());
		// mCompositions.push(new AIVisitorStackElement(false));
	}

	@Override
	public void visited(StatementSequence c) {
		// mLogger.debug(mDebugOuputNesting + " States:\n" +
		// mResultingStates.toString());
		// mDebugOuputNesting = mDebugOuputNesting.substring(0,
		// mDebugOuputNesting.length() - 1);
		// mLogger.debug(mDebugOuputNesting + "< StatementSequence END");
	}

	@Override
	public void visit(Summary c) {
		// summaries are not supported, instead the call
		// must be processed
		// so this edge may not yield any states
		mResultingStates = new ArrayList<StackState>();
	}

	@Override
	public IStatementVisitor getStatementVisitor() {
		/**
		 * For implementing the IRCFGVisitor. Returns itself, since it also
		 * implements the IStatementVisitor.
		 */
		return this;
	}

	/* ----- ----- ----- ---------- ----- ----- ----- */
	/* ----- ----- ----- Statements ----- ----- ----- */
	/* ----- ----- ----- ---------- ----- ----- ----- */

	@Override
	public boolean visitStatement(Statement e) {
		if (mResultingStates.size() == 0) {
			// mLogger.debug(">> Ignore Statement (bottom)");
			return false;
		}
		// mLogger.debug("Statement: " + e.toString());
		// mDebugOuputNesting += " ";
		// mLogger.debug("States before:\n" +
		// StackState.toString(mResultingStates));
		return true;
	}

	@Override
	public void visitedStatement(Statement e) {
		// mLogger.debug("States afterwards:\n" +
		// StackState.toString(mResultingStates));
		// mDebugOuputNesting = mDebugOuputNesting.substring(0,
		// mDebugOuputNesting.length() - 1);
		// mLogger.debug(mDebugOuputNesting + "< Statement END");
	}

	@Override
	public void visit(AssertStatement s) {
		// mLogger("Applying assert: " + s.toString());

		for (StackState ss : mResultingStates) {
			if (!mDomain.checkAssert(ss.getCurrentScope().getState(), s.getFormula())) {
				mViolatedAssert = true;
				mResult = "assert was not fulfilled: " + s.getFormula() + " for ss";
				// mResultingState = null;
			}
		}
		if (mViolatedAssert) {
			// make it "bottom"
			mResultingStates.clear();
		}
	}

	@Override
	public void visit(AssignmentStatement s) {
		// apply the assignment on every available state
		List<StackState> newResultingStates = new ArrayList<StackState>();
		for (StackState state : mResultingStates) {
			// apply the formula on a copy of the topmost state
			IAbstractState resultingState = state.getCurrentScope().getState();

			LeftHandSide[] lhs = s.getLhs();
			Expression[] rhs = s.getRhs();

			if (lhs.length != rhs.length) {
				mLogger.warn(String.format("%s lhs and rhs size mismatch!", s.getClass()));
				return;
			}

			for (int i = 0; i < lhs.length; i++) {
				LeftHandSide l = lhs[i];
				Expression r = rhs[i];
				TypedAbstractVariable variable;
				if (l instanceof ArrayLHS) {
					throw new UnsupportedOperationException();
				} else if (l instanceof VariableLHS) {
					VariableLHS var = (VariableLHS) l;
					variable = new TypedAbstractVariable(var.getIdentifier(), var.getDeclarationInformation(),
							var.getType());
				} else {
					throw new UnsupportedOperationException(
							String.format("Unsupported LeftHandSide type %s", l.getClass()));
				}
				resultingState = mDomain.applyExpression(resultingState, variable, r);
			}
			if (!resultingState.isBottom()) {
				newResultingStates.add(state.increment(resultingState));
			}
		}
		mResultingStates = newResultingStates;
	}

	@Override
	public void visit(AssumeStatement s) {
		// apply the assume statement on every available state
		List<StackState> newResultingStates = new ArrayList<StackState>();
		for (StackState state : mResultingStates) {
			// apply the formula on a copy of the topmost state
			List<IAbstractState> resultingStates = mDomain.applyAssume(state.getCurrentScope().getState(),
					s.getFormula());

			// there can be more than one resulting state (due to
			// or-expressions)
			for (IAbstractState res : resultingStates) {
				if (!res.isBottom()) {
					// set the result to a copy of the state
					newResultingStates.add(state.increment(res));
				}
			}
		}
		mResultingStates = newResultingStates;
	}

	@Override
	public void visit(HavocStatement s) {
		// apply the assume statement on every available state
		List<StackState> newResultingStates = new ArrayList<StackState>();
		for (StackState state : mResultingStates) {
			// apply the formula on a copy of the topmost state
			IAbstractState resultingState = state.getCurrentScope().getState();

			for (VariableLHS lhs : s.getIdentifiers()) {
				// mLogger.debug("Havoc : " + lhs.getIdentifier());

				TypedAbstractVariable variable = new TypedAbstractVariable(lhs.getIdentifier(),
						lhs.getDeclarationInformation(), lhs.getType());
				resultingState = mDomain.applyHavoc(resultingState, variable);
			}

			// set the result to a copy of the state
			// havoc cannot cause bottom states
			newResultingStates.add(state.increment(resultingState));
		}
		mResultingStates = newResultingStates;
	}

	@Override
	public void visit(BreakStatement s) {
		// nothing to do
	}

	@Override
	public void visit(CallStatement s) {
		String procedureName = s.getMethodName();
		// mLogger.debug(String.format("CALL: %s", procedureName));

		// fetch method declaration to get input parameters
		List<Declaration> methodDecList = mSymbolTable.getFunctionOrProcedureDeclaration(procedureName);

		if (methodDecList.size() < 1) {
			error(String.format("Procedure declaration \"%s\" not found.", procedureName));
			return;
		}

		Declaration methodDec = methodDecList.get(0);
		VarList[] parameters = null;
		if (methodDec instanceof FunctionDeclaration) {
			FunctionDeclaration functionDec = (FunctionDeclaration) methodDec;
			parameters = functionDec.getInParams();
		} else if (methodDec instanceof Procedure) {
			Procedure procedureDec = (Procedure) methodDec;
			parameters = procedureDec.getInParams();
		} else {
			error(String.format("Unknown method declaration kind \"%s\" encountered.", methodDec));
			return;
		}

		// formal parameters of the call statement
		Expression[] arguments = s.getArguments();

		// match arguments and expressions
		List<TypedAbstractVariable> targetVariables = new ArrayList<TypedAbstractVariable>();
		List<Expression> argumentExpressions = new ArrayList<Expression>();
		if (!matchArguments(parameters, arguments, null, targetVariables, argumentExpressions)) {
			return;
		}

		// apply the call statement on every available state
		for (StackState state : mResultingStates) {
			// hand over global variables as arguments
			List<TypedAbstractVariable> allTargetVariables = new ArrayList<TypedAbstractVariable>(targetVariables);
			List<Expression> allArgumentExpressions = new ArrayList<Expression>(argumentExpressions);
			addGlobals(state, allTargetVariables, allArgumentExpressions);

			// apply the formula on a copy of the topmost state
			// this way
			IAbstractState oldState = state.getCurrentScope().getState();
			// create a new state for the new layer
			IAbstractState resultingState = mDomain.createState();

			// compute the new state
			// and add a new scope (copies the actual)
			mDomain.applyExpressionScoped(resultingState, oldState, allTargetVariables, allArgumentExpressions);

			state.pushStackLayer(s, resultingState);
		}
	}

	@Override
	public void visitReturn(CallStatement callStatement) {
		String procedureName = callStatement.getMethodName();
		// mLogger.debug(String.format("RETURN: %s", procedureName));

		// it is assumed that all states have the same call stack history
		// since this visitor is only called with one state
		CallStatement currentScopeCall = mResultingStates.get(0).getCurrentScope().getCallStatement();
		if (currentScopeCall != callStatement) {
			// mLogger.debug("Return does not belong to Call");
			mResultingStates = new ArrayList<StackState>();
			return;
		}

		// fetch method declaration to get input parameters
		List<Declaration> methodDecList = mSymbolTable.getFunctionOrProcedureDeclaration(procedureName);

		if (methodDecList.size() < 1) {
			error(String.format("Procedure declaration \"%s\" not found.", procedureName));
			return;
		}

		Declaration methodDec = methodDecList.get(0);
		VarList[] parameters = null;
		if (methodDec instanceof Procedure) {
			Procedure procedureDec = (Procedure) methodDec;
			parameters = procedureDec.getOutParams();
		} else {
			error(String.format("Unknown method declaration kind \"%s\" encountered.", methodDec));
			return;
		}

		// where to write the out parameters to
		VariableLHS[] lhsVariables = callStatement.getLhs();

		// match arguments and expressions
		List<TypedAbstractVariable> targetVariables = new ArrayList<TypedAbstractVariable>();
		List<Expression> argumentExpressions = new ArrayList<Expression>();
		if (!matchArguments(parameters, null, lhsVariables, targetVariables, argumentExpressions)) {
			return;
		}

		// apply the call statement on every available state
		for (StackState state : mResultingStates) {
			// hand over global variables as arguments
			List<TypedAbstractVariable> allTargetVariables = new ArrayList<TypedAbstractVariable>(targetVariables);
			List<Expression> allArgumentExpressions = new ArrayList<Expression>(argumentExpressions);
			addGlobals(state, allTargetVariables, allArgumentExpressions);

			// apply the formula on a the top scope and save
			// save them in the variables of the scope above
			IAbstractState topScope = state.getCurrentScope().getState();
			state.popStackLayer();
			IAbstractState oldScope = state.getCurrentScope().getState();

			mDomain.applyExpressionScoped(oldScope, topScope, allTargetVariables, allArgumentExpressions);

			state.increment(oldScope);
		}
	}

	private void addGlobals(StackState state, List<TypedAbstractVariable> allTargetVariables,
			List<Expression> allArgumentExpressions) {
		// Add global variables
		for (Entry<String, Declaration> entry : mSymbolTable.getGlobalVariables().entrySet()) {
			if (allTargetVariables.contains(new AbstractVariable(entry.getKey()))) {
				continue; // do not override global variables if they are a left
							// hand side variable
			}

			AbstractVariable abstGlobal = new AbstractVariable(entry.getKey());
			if (state.getCurrentState().hasVariable(abstGlobal)) {
				TypedAbstractVariable global = state.getCurrentState().getTypedVariable(abstGlobal);

				if (global == null) {
					throw new RuntimeException();
				}
				allTargetVariables.add(global);
				VariableDeclaration varDec = (VariableDeclaration) entry.getValue();
				allArgumentExpressions.add(new IdentifierExpression(varDec.getLocation(), global.getType(),
						entry.getKey(), global.getDeclaration()));
			}

		}
	}

	/**
	 * Matches arguments and expressions. Into two lists. Two possibilities:
	 * expressions of "arguments" into variables of "parameters" or:
	 * "parameters" as expressions into variables of lhsVariables
	 * 
	 * @param parameters
	 * @param arguments
	 * @param targetVariables
	 * @param argumentExpressions
	 * @param callStatement
	 * 
	 * @return
	 */
	private boolean matchArguments(VarList[] parameters, Expression[] arguments, VariableLHS[] lhsVariables,
			List<TypedAbstractVariable> targetVariables, List<Expression> argumentExpressions) {
		if (parameters == null) {
			mLogger.warn(String.format("Parameters of not found."));
			return false;
		}
		int nofVariables = arguments == null ? lhsVariables.length : arguments.length;

		int currentExpression = 0;
		for (int p = 0; p < parameters.length; p++) {
			// for each type of parameter there may be several
			// identifiers
			String[] identifiers = parameters[p].getIdentifiers();
			IType type = parameters[p].getType().getBoogieType();
			for (int i = 0; i < identifiers.length; i++) {
				if (currentExpression >= nofVariables) {
					// this may not happen
					error(String.format("Invalid number of arguments for method call!"));
					return false;
				}

				if (arguments != null) // call
				{
					// match the argument expression pair
					argumentExpressions.add(arguments[currentExpression]);
					targetVariables.add(new TypedAbstractVariable(identifiers[i], null, type));
				} else if (lhsVariables != null) // return
				{
					// match the argument expression pair
					argumentExpressions.add(new IdentifierExpression(null, type, identifiers[i], null));
					targetVariables.add(evaluateLeftHandSide(lhsVariables[currentExpression]));
				} else {
					throw new RuntimeException();
				}

				currentExpression++;
			}
		}
		return true;
	}

	private TypedAbstractVariable evaluateLeftHandSide(LeftHandSide lhs) {
		if (lhs instanceof ArrayLHS) {
			return visit((ArrayLHS) lhs);
		} else if (lhs instanceof VariableLHS) {
			return visit((VariableLHS) lhs);
		} else {
			throw new UnsupportedOperationException(String.format("Unsupported LeftHandSide type %s", lhs.getClass()));
		}
	}

	private TypedAbstractVariable visit(VariableLHS lhs) {
		return new TypedAbstractVariable(lhs.getIdentifier(), lhs.getDeclarationInformation(), lhs.getType());
	}

	private TypedAbstractVariable visit(ArrayLHS lhs) {
		mLogger.warn(String.format("Unsupported LeftHandSide type: %s", lhs.getClass()));
		throw new UnsupportedOperationException();
	}

	/** ------------ Helper functions ------------ **/

	private void error(String err) {
		mLogger.error(err);
		mError = err;
		return;
	}

	@Override
	public void visit(GotoStatement s) {
		/**
		 * this should not occur
		 */
		throw new UnsupportedOperationException();
	}

	@Override
	public void visit(IfStatement s) {
		/**
		 * this should not occur
		 */
		throw new UnsupportedOperationException();
	}

	@Override
	public void visit(Label s) {
		// mLogger("Label : " + s.getName());
	}

	@Override
	public void visit(WhileStatement s) {
		/**
		 * this should not occur
		 */
		throw new UnsupportedOperationException();
	}

}
