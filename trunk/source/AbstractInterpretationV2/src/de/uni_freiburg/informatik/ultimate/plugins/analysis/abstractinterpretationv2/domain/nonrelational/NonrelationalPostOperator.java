/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ITermProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The post operator of the interval domain for {@link IBoogieVar}s.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class NonrelationalPostOperator<STATE extends NonrelationalState<STATE, V, IBoogieVar>, V extends INonrelationalValue<V>>
		implements IAbstractPostOperator<STATE, IcfgEdge, IBoogieVar> {

	private final ILogger mLogger;
	private final RcfgStatementExtractor mStatementExtractor;
	private final NonrelationalStatementProcessor<STATE, V> mStatementProcessor;
	private final BoogieSymbolTable mSymbolTable;
	private final int mParallelStates;
	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	private final Boogie2SMT mBoogie2Smt;
	private final BoogieIcfgContainer mRootAnnotation;
	private final CallInfoCache mCallInfoCache;

	protected NonrelationalPostOperator(final ILogger logger, final BoogieSymbolTable symbolTable,
			final Boogie2SmtSymbolTable bpl2smtSymbolTable,
			final NonrelationalStatementProcessor<STATE, V> statementProcessor, final int parallelStates,
			final Boogie2SMT boogie2Smt, final BoogieIcfgContainer rootAnnotation) {
		mLogger = logger;
		mStatementExtractor = new RcfgStatementExtractor();
		mBoogie2SmtSymbolTable = bpl2smtSymbolTable;
		mStatementProcessor = statementProcessor;
		mSymbolTable = symbolTable;
		mParallelStates = parallelStates;
		mBoogie2Smt = boogie2Smt;
		mRootAnnotation = rootAnnotation;
		mCallInfoCache = new CallInfoCache();
	}

	@Override
	public List<STATE> apply(final STATE oldstate, final IcfgEdge transition) {
		assert oldstate != null;
		assert !oldstate.isBottom() : "You should not need to calculate post of a bottom state";
		assert transition != null;
		final IcfgEdge transitionLabel = transition.getLabel();

		if (transitionLabel instanceof Summary) {
			if (!((Summary) transitionLabel).calledProcedureHasImplementation()) {
				// TODO fix WORKAROUND unsoundness for summary code blocks without procedure implementation
				throw new UnsupportedOperationException("Summary for procedure without implementation: "
						+ BoogiePrettyPrinter.print(((Summary) transitionLabel).getCallStatement()));
			}
			return handleReturnTransition(oldstate, oldstate, transitionLabel);
		} else if (transitionLabel instanceof IIcfgInternalTransition<?>) {
			return handleInternalTransition(oldstate, transitionLabel);
		} else if (transitionLabel instanceof Call) {
			return handleCallTransition(oldstate, oldstate, (Call) transitionLabel);
		} else if (transitionLabel instanceof Return) {
			return handleReturnTransition(oldstate, oldstate, transitionLabel);
		} else {
			throw new UnsupportedOperationException("Unknown transition type: " + transitionLabel.getClass());
		}
	}

	@Override
	public List<STATE> apply(final STATE stateBeforeLeaving, final STATE stateAfterLeaving, final IcfgEdge transition) {
		assert stateBeforeLeaving != null;
		assert !stateBeforeLeaving.isBottom() : "You should not need to calculate post of a bottom state (BL)";
		assert stateAfterLeaving != null;
		assert !stateAfterLeaving.isBottom() : "You should not need to calculate post of a bottom state (AL)";
		assert transition != null;

		final IcfgEdge transitionLabel = transition.getLabel();

		assert transitionLabel instanceof Call || transitionLabel instanceof Return
				|| transitionLabel instanceof Summary : "Cannot calculate hierachical post for non-hierachical transition";

		if (transitionLabel instanceof Call) {
			final Call call = (Call) transitionLabel;
			return handleCallTransition(stateBeforeLeaving, stateAfterLeaving, call);
		} else if (transitionLabel instanceof Return || transitionLabel instanceof Summary) {
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, transitionLabel);
		} else {
			throw new UnsupportedOperationException(
					"Nonrelational domains do not support context switches other than Call and Return (yet)");
		}
	}

	private List<STATE> handleCallTransition(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final Call call) {

		final CallStatement callStatement = call.getCallStatement();
		final CallInfo callInfo = mCallInfoCache.getCallInfo(callStatement, stateBeforeLeaving);
		// If there are no arguments, we don't need to rewrite states.
		if (callInfo.getInParamAssign() == null) {
			return addOldvars(Collections.singletonList(stateAfterLeaving), callInfo.getOldVarAssign());
		}

		// process assignment of expressions in old scope to inparams of procedure
		final STATE interimState = stateBeforeLeaving.addVariables(callInfo.getTempInParams());
		final List<STATE> result =
				mStatementProcessor.process(interimState, callInfo.getInParamAssign(), callInfo.getTempInParamUses());
		if (result.isEmpty()) {
			throw new AssertionError("The assignment operation resulted in 0 states.");
		}

		final List<IBoogieVar> realParamVars = callInfo.getRealInParams();

		// assign values of expression evaluation to actual inparams
		final List<STATE> returnList = new ArrayList<>();
		for (final STATE resultState : result) {
			STATE returnState = stateAfterLeaving;

			for (int i = 0; i < realParamVars.size(); i++) {
				final IBoogieVar tempVar = callInfo.getTempInParams().get(i);
				final IBoogieVar realVar = realParamVars.get(i);

				final STATE finalReturnState = returnState;

				// TODO: Add array support.
				final Function<IBoogieVar, STATE> varFunction =
						var -> finalReturnState.setValue(realVar, resultState.getValue(var));
				final Function<IBoogieVar, STATE> boolFunction =
						var -> finalReturnState.setBooleanValue(realVar, resultState.getBooleanValue(tempVar));

				returnState = TypeUtils.applyVariableFunction(varFunction, boolFunction, null, tempVar);
			}

			returnList.add(returnState);
		}
		return addOldvars(NonrelationalUtils.mergeStatesIfNecessary(returnList, mParallelStates),
				callInfo.getOldVarAssign());
	}

	/**
	 * Computes the result of applying the return transition with a given state before leaving the inner scope (before
	 * the return) and the previous state after the method has been called.
	 *
	 * <p>
	 * This method updates the state after leaving with the return value of the called method and adapts the different
	 * parameter expressions from the calls according to the effect in the method itself.
	 * </p>
	 *
	 * @param stateBeforeLeaving
	 * @param stateAfterLeaving
	 * @param returnTransition
	 * @return
	 */
	private List<STATE> handleReturnTransition(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final IcfgEdge transition) {
		final CallStatement correspondingCall = getCorrespondingCall(transition);
		final List<STATE> returnList = new ArrayList<>();

		final Procedure procedure = getProcedure(correspondingCall.getMethodName());
		final Pair<Deque<V>, Deque<BooleanValue>> outVals = getOutParamValues(procedure, stateBeforeLeaving);
		final List<ITermProvider> inVals = getInParamValues(procedure, stateBeforeLeaving);
		final VariableLHS[] lhs = correspondingCall.getLhs();
		final Expression[] args = correspondingCall.getArguments();

		if (outVals.getFirst().size() + outVals.getSecond().size() != lhs.length) {
			throw new UnsupportedOperationException("The expected number of return variables (" + lhs.length
					+ ") is different from the function's number of return variables (" + outVals.getFirst().size()
					+ " vals, " + outVals.getSecond().size() + " bools).");
		}

		if (inVals.size() != args.length) {
			throw new UnsupportedOperationException("The expected number of input expressions (" + args.length
					+ ") is different from the function's number of input parameters (" + inVals.size() + ").");
		}

		// Gather return variables and values for the return abstract state
		final List<IBoogieVar> updateVarNames = new ArrayList<>();
		for (final VariableLHS varLhs : lhs) {
			final BoogieVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(varLhs.getIdentifier(),
					varLhs.getDeclarationInformation(), false);
			assert boogieVar != null;
			updateVarNames.add(boogieVar);
		}

		final List<Pair<IBoogieVar, V>> updateVars = new ArrayList<>();
		final List<Pair<IBoogieVar, BooleanValue>> updateBools = new ArrayList<>();

		// TODO: Add array support.
		final Consumer<IBoogieVar> varConsumer =
				var -> updateVars.add(new Pair<>(var, outVals.getFirst().removeFirst()));
		final Consumer<IBoogieVar> boolConsumer =
				var -> updateBools.add(new Pair<>(var, outVals.getSecond().removeFirst()));

		// Assign to each return variable the corresponding return value
		for (final IBoogieVar boogieVar : updateVarNames) {
			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, boogieVar);
		}
		assert outVals.getFirst().size() == 0;
		assert outVals.getSecond().size() == 0;

		final List<Expression> inputParameterExpressionTerms = new ArrayList<>();

		// Update input expressions wrt. parameter values at the end of the executed procedure
		for (int i = 0; i < inVals.size(); i++) {
			final ITermProvider inValue = inVals.get(i);
			final Expression inExpression = args[i];

			final IIdentifierTranslator[] translators = new IIdentifierTranslator[] { new SimpleTranslator(),
					mBoogie2Smt.new ConstOnlyIdentifierTranslator() };

			final Term expressionTerm =
					mBoogie2Smt.getExpression2Term().translateToTerm(translators, inExpression).getTerm();

			final Term valueTerm = inValue.getTerm(mBoogie2Smt.getScript(), expressionTerm.getSort(), expressionTerm);

			final Expression termExpression = mBoogie2Smt.getTerm2Expression().translate(valueTerm);

			assert termExpression.getType() == BoogieType.TYPE_BOOL;

			inputParameterExpressionTerms.add(termExpression);
		}

		final List<STATE> rets = new ArrayList<>();

		// Construct conjunction of input parameter expressions
		if (inputParameterExpressionTerms.size() > 0) {
			Expression current = inputParameterExpressionTerms.get(0);

			for (int i = 1; i < inputParameterExpressionTerms.size(); i++) {
				current = new BinaryExpression(correspondingCall.getLocation(), Operator.LOGICAND, current,
						inputParameterExpressionTerms.get(i));

				if (current.getType() == null) {
					current.setType(BoogieType.TYPE_BOOL);
				}
			}

			// Construct an assume statement
			final AssumeStatement assume = new AssumeStatement(correspondingCall.getLocation(), current);
			final List<Statement> stmtList = new ArrayList<>();
			stmtList.add(assume);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("    Computing post after return for arguments with statement: "
						+ BoogiePrettyPrinter.print(assume));
			}

			final IcfgEdge newPostBlock = mRootAnnotation.getCodeBlockFactory().constructStatementSequence(null, null,
					stmtList, Origin.IMPLEMENTATION);

			final List<STATE> postResults = apply(stateAfterLeaving, newPostBlock);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("    Resulting post states: "
						+ postResults.stream().map(r -> r.toLogString()).collect(Collectors.toList()));
			}
			rets.addAll(postResults);
		}

		if (rets.size() == 0) {
			rets.add(stateAfterLeaving);
		}

		// Create arrays for state update functions.
		final IBoogieVar[] updateVarNameArray = updateVars.stream().map(entry -> entry.getFirst())
				.collect(Collectors.toList()).toArray(new IBoogieVar[updateVars.size()]);
		final V[] updateVarValsArray = updateVars.stream().map(entry -> entry.getSecond()).collect(Collectors.toList())
				.toArray(stateAfterLeaving.getArray(updateVars.size()));
		final IBoogieVar[] updateBoolNameArray = updateBools.stream().map(entry -> entry.getFirst())
				.collect(Collectors.toList()).toArray(new IBoogieVar[updateBools.size()]);
		final BooleanValue[] updateBoolValsArray = updateBools.stream().map(entry -> entry.getSecond())
				.collect(Collectors.toList()).toArray(new BooleanValue[updateBools.size()]);

		for (final STATE s : rets) {
			// TODO: Implement better handling of arrays.
			returnList.add(s.setMixedValues(updateVarNameArray, updateVarValsArray, updateBoolNameArray,
					updateBoolValsArray, new IBoogieVar[0], stateAfterLeaving.getArray(0)));
		}

		return NonrelationalUtils.mergeStatesIfNecessary(returnList, mParallelStates);
	}

	private List<STATE> handleInternalTransition(final STATE oldstate, final IcfgEdge transition) {
		List<STATE> currentStates = new ArrayList<>();
		currentStates.add(oldstate);
		final List<Statement> statements = mStatementExtractor.process(transition.getLabel());

		for (final Statement stmt : statements) {
			final List<STATE> afterProcessStates = new ArrayList<>();
			for (final STATE currentState : currentStates) {
				final List<STATE> processed = mStatementProcessor.process(currentState, stmt);
				for (final STATE s : processed) {
					if (!s.isBottom()) {
						afterProcessStates.add(s);
					}
				}
			}
			currentStates = afterProcessStates;
		}

		if (currentStates.isEmpty()) {
			if (!oldstate.getVariables().isEmpty()) {
				currentStates.add(oldstate.bottomState());
			}
			return currentStates;
		}

		return NonrelationalUtils.mergeStatesIfNecessary(currentStates, mParallelStates);
	}

	private static CallStatement getCorrespondingCall(final IcfgEdge transition) {
		if (transition instanceof Return) {
			return ((Return) transition).getCallStatement();
		} else if (transition instanceof Summary) {
			return ((Summary) transition).getCallStatement();
		} else {
			throw new IllegalArgumentException("Transition " + transition.getClass() + " has no corresponding call");
		}
	}

	/**
	 * After all parameters of a call are assigned, we add new oldvar values to all vars which are modified by the new
	 * procedure.
	 * 
	 * @param pendingPostStates
	 * @param oldVarAssign
	 * @return
	 */
	private List<STATE> addOldvars(final List<STATE> pendingPostStates, final Statement oldVarAssign) {
		if (oldVarAssign == null) {
			return pendingPostStates;
		}
		final List<STATE> postStates = new ArrayList<>();

		for (final STATE pendingPostState : pendingPostStates) {
			postStates.addAll(mStatementProcessor.process(pendingPostState, oldVarAssign));
		}

		return NonrelationalUtils.mergeStatesIfNecessary(postStates, mParallelStates);
	}

	/**
	 * Creates a map of Integers -&gt; Identifiers for a given desired number of variables. The created identifiers are
	 * unique temporary variable identifiers. It is ensured that the created identifiers do not already occur in the
	 * current state.
	 *
	 * @param argNum
	 *            The number of temporary variables to create.
	 * @param state
	 *            The current state.
	 * @return A map containing for each index of the call statement's argument
	 */
	private static List<String> getArgumentTemporaries(final int argNum, final Set<String> reservedNames) {
		final List<String> rtr = new ArrayList<>(argNum);

		final StringBuilder paramBuilder = new StringBuilder("param_");
		boolean uniqueFound = false;

		while (!uniqueFound) {
			final String currentPrefix = paramBuilder.toString();
			for (int i = 0; i < argNum; i++) {
				final String currentParamName = currentPrefix + String.valueOf(i);
				if (reservedNames.contains(currentParamName)) {
					paramBuilder.append('_');
					break;
				}
			}
			uniqueFound = true;
		}

		final String finalPrefix = paramBuilder.toString();
		for (int i = 0; i < argNum; i++) {
			rtr.add(finalPrefix + String.valueOf(i));
		}

		return rtr;
	}

	private Procedure getProcedure(final String procedureName) {

		return mSymbolTable.getFunctionOrProcedureDeclaration(procedureName).stream()
				.filter(decl -> decl instanceof Procedure).map(decl -> (Procedure) decl)
				.filter(proc -> proc.getBody() != null).findFirst().orElseThrow(() -> new UnsupportedOperationException(
						"Only uninterpreted functions available for " + procedureName));
	}

	private Pair<Deque<V>, Deque<BooleanValue>> getOutParamValues(final Procedure procedure,
			final STATE stateBeforeLeaving) {
		// functions are already inlined and if there are procedure and implementation declaration for a proc, we know
		// that we only get the implementation from the FXPE
		final Deque<V> vals = new ArrayDeque<>();
		final Deque<BooleanValue> boolVals = new ArrayDeque<>();

		// TODO: Add array support.
		final Consumer<IBoogieVar> varConsumer = var -> vals.add(stateBeforeLeaving.getValue(var));
		final Consumer<IBoogieVar> boolConsumer = var -> boolVals.add(stateBeforeLeaving.getBooleanValue(var));

		for (final VarList list : procedure.getOutParams()) {
			for (final String s : list.getIdentifiers()) {
				final IBoogieVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(s, procedure.getIdentifier(), false);
				assert boogieVar != null;
				TypeUtils.consumeVariable(varConsumer, boolConsumer, null, boogieVar);
			}
		}

		return new Pair<>(vals, boolVals);
	}

	private List<ITermProvider> getInParamValues(final Procedure procedure, final STATE stateBeforeLeaving) {
		final List<ITermProvider> vals = new ArrayList<>();

		// TODO: Add array support.
		final Consumer<IBoogieVar> varConsumer = var -> vals.add(stateBeforeLeaving.getValue(var));
		final Consumer<IBoogieVar> boolConsumer = var -> vals.add(stateBeforeLeaving.getBooleanValue(var));

		for (final VarList list : procedure.getInParams()) {
			for (final String s : list.getIdentifiers()) {
				final IBoogieVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(s,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedure.getIdentifier()), false);
				assert boogieVar != null;
				TypeUtils.consumeVariable(varConsumer, boolConsumer, null, boogieVar);
			}
		}

		return vals;
	}

	private class SimpleTranslator implements IIdentifierTranslator {
		@Override
		public Term getSmtIdentifier(final String id, final DeclarationInformation declInfo, final boolean isOldContext,
				final BoogieASTNode boogieASTNode) {
			IProgramVarOrConst boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(id, declInfo, isOldContext);
			if (boogieVar == null) {
				boogieVar = mBoogie2SmtSymbolTable.getBoogieConst(id);
			}
			assert boogieVar != null : "Unknown symbol: " + id;
			return boogieVar.getTerm();
		}
	}

	private class CallInfoCache {
		private final Map<CallStatement, CallInfo> mCallInfoCache;

		private CallInfoCache() {
			mCallInfoCache = new HashMap<>();
		}

		private CallInfo getCallInfo(final CallStatement callStatement, final STATE stateBeforeLeaving) {
			final CallInfo callAssignment = mCallInfoCache.get(callStatement);
			if (callAssignment != null) {
				return callAssignment;
			}
			final CallInfo newCallAssignment = createCallInfo(callStatement, stateBeforeLeaving);
			mCallInfoCache.put(callStatement, newCallAssignment);
			return newCallAssignment;
		}

		private CallInfo createCallInfo(final CallStatement callStatement, final STATE stateBeforeLeaving) {
			final Expression[] args = callStatement.getArguments();
			final List<IBoogieVar> realInParams = getInParams(callStatement);
			final AssignmentStatement oldVarAssign = getOldvarAssign(callStatement);

			// If there are no arguments, we don't need to rewrite states and thus no inparam assign.
			if (args.length == 0) {
				return new CallInfo(realInParams, oldVarAssign);
			}

			// create a multi-assignment statement that assigns each procedure argument (expression) to a temporary
			// variable
			final List<String> tmpParamNames = getArgumentTemporaries(args.length, stateBeforeLeaving.getVariables()
					.stream().map(IBoogieVar::getGloballyUniqueId).collect(Collectors.toSet()));
			final List<LeftHandSide> idents = new ArrayList<>();
			final Map<LeftHandSide, IBoogieVar> tmpVarUses = new HashMap<>();
			final List<IBoogieVar> tmpParamVars = new ArrayList<>();
			final ILocation loc = callStatement.getLocation();
			for (int i = 0; i < args.length; i++) {
				final String name = tmpParamNames.get(i);
				final IBoogieVar boogieVar = AbsIntUtil.createTemporaryIBoogieVar(name, args[i].getType());
				final VariableLHS lhs = new VariableLHS(loc, name);
				tmpParamVars.add(boogieVar);
				tmpVarUses.put(lhs, boogieVar);
				idents.add(lhs);
			}

			final AssignmentStatement inParamTmpAssign =
					new AssignmentStatement(loc, idents.toArray(new LeftHandSide[idents.size()]), args);
			return new CallInfo(realInParams, oldVarAssign, inParamTmpAssign, tmpParamVars, tmpVarUses);
		}

		/**
		 * Create an assignment for oldvar values at the beginning of a procedure: <code>
		 * old(x1),...,old(xn) := x1, .... , xn;
		 * </code>
		 */
		private AssignmentStatement getOldvarAssign(final CallStatement callStatement) {
			final String methodName = callStatement.getMethodName();
			final Set<IProgramNonOldVar> modifiableGlobals =
					mRootAnnotation.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(methodName);
			final int modglobsize = modifiableGlobals.size();
			if (modglobsize == 0) {
				return null;
			}
			final LeftHandSide[] lhs = new LeftHandSide[modglobsize];
			final Expression[] rhs = new Expression[modglobsize];
			int i = 0;
			final ILocation loc = callStatement.getLocation();
			for (final IProgramNonOldVar modGlob : modifiableGlobals) {

				final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
				final IBoogieType bType =
						mSymbolTable.getTypeForVariableSymbol(modGlob.getGloballyUniqueId(), StorageClass.GLOBAL, null);
				lhs[i] = new VariableLHS(loc, bType, modGlob.getOldVar().getGloballyUniqueId(), declInfo);
				rhs[i] = new IdentifierExpression(loc, bType, modGlob.getGloballyUniqueId(), declInfo);
				++i;
			}
			return new AssignmentStatement(loc, lhs, rhs);
		}

		private List<IBoogieVar> getInParams(final CallStatement callStatement) {
			final Procedure procedure = getProcedure(callStatement.getMethodName());
			assert procedure != null;
			final VarList[] inParams = procedure.getInParams();
			final List<IBoogieVar> realParamVars = new ArrayList<>();

			for (final VarList varlist : inParams) {
				for (final String var : varlist.getIdentifiers()) {
					final IBoogieVar bVar =
							mBoogie2SmtSymbolTable.getBoogieVar(var, callStatement.getMethodName(), true);
					assert bVar != null;
					realParamVars.add(bVar);
				}
			}

			if (callStatement.getArguments().length != realParamVars.size()) {
				throw new UnsupportedOperationException(
						"The number of the expressions in the call statement arguments does not correspond to the length of the number of arguments in the symbol table.");
			}
			return realParamVars;
		}
	}

	private static class CallInfo {
		private final AssignmentStatement mInParamAssign;
		private List<IBoogieVar> mTmpVars;
		private Map<LeftHandSide, IBoogieVar> mTmpVarUses;
		private List<IBoogieVar> mRealInParams;
		private AssignmentStatement mOldVarAssign;

		private CallInfo(final List<IBoogieVar> realInParams, final AssignmentStatement oldVarAssign) {
			this(realInParams, oldVarAssign, null, Collections.emptyList(), Collections.emptyMap());
		}

		private CallInfo(final List<IBoogieVar> realInParams, final AssignmentStatement oldVarAssign,
				final AssignmentStatement inParamAssign, final List<IBoogieVar> tmpVars,
				final Map<LeftHandSide, IBoogieVar> tmpVarUses) {
			mOldVarAssign = oldVarAssign;
			mInParamAssign = inParamAssign;
			mTmpVars = Collections.unmodifiableList(tmpVars);
			mTmpVarUses = Collections.unmodifiableMap(tmpVarUses);
			mRealInParams = Collections.unmodifiableList(realInParams);
		}

		public List<IBoogieVar> getRealInParams() {
			return mRealInParams;
		}

		public List<IBoogieVar> getTempInParams() {
			return mTmpVars;
		}

		public Map<LeftHandSide, IBoogieVar> getTempInParamUses() {
			return mTmpVarUses;
		}

		public AssignmentStatement getInParamAssign() {
			return mInParamAssign;
		}

		public AssignmentStatement getOldVarAssign() {
			return mOldVarAssign;
		}
	}
}
