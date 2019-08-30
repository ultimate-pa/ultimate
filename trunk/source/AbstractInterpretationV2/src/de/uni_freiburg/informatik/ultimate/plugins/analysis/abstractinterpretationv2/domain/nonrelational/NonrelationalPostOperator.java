/*
 * Copyright (C) 2015-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 University of Freiburg
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
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ITermProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.CallInfoCache;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.CallInfoCache.CallInfo;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TemporaryBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A basic post operator for non-relational domains that operate on Boogie code and {@link IProgramVar}s. It relies on
 * {@link INonrelationalValue} for most of its operations.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class NonrelationalPostOperator<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		implements IAbstractPostOperator<STATE, IcfgEdge> {

	private final ILogger mLogger;
	private final RcfgStatementExtractor mStatementExtractor;
	private final NonrelationalStatementProcessor<STATE, V> mStatementProcessor;
	private final BoogieSymbolTable mSymbolTable;
	private final int mParallelStates;
	private final IBoogieSymbolTableVariableProvider mBoogie2SmtSymbolTable;
	private final Boogie2SMT mBoogie2Smt;
	private final CallInfoCache mCallInfoCache;
	private AbsIntBenchmark<IcfgEdge> mAbsIntBenchmark = null;
	private final MappedTerm2Expression mMappedTerm2Expression;
	private final NonrelationalEvaluator<STATE, V> mEvaluator;

	protected NonrelationalPostOperator(final ILogger logger, final BoogieSymbolTable symbolTable,
			final IBoogieSymbolTableVariableProvider bpl2SmtSymbolTable, final int parallelStates,
			final Boogie2SMT boogie2Smt, final CfgSmtToolkit cfgSmtToolkit,
			final NonrelationalEvaluator<STATE, V> evaluator) {
		mLogger = logger;
		mStatementExtractor = new RcfgStatementExtractor();
		mBoogie2SmtSymbolTable = bpl2SmtSymbolTable;
		mStatementProcessor =
				new NonrelationalStatementProcessor<>(logger, boogie2Smt.getBoogie2SmtSymbolTable(), evaluator);
		mEvaluator = evaluator;
		mSymbolTable = symbolTable;
		mParallelStates = parallelStates;
		mBoogie2Smt = boogie2Smt;
		mCallInfoCache = new CallInfoCache(cfgSmtToolkit, symbolTable);
		mMappedTerm2Expression = new MappedTerm2Expression(mBoogie2Smt.getTypeSortTranslator(),
				mBoogie2Smt.getBoogie2SmtSymbolTable(), mBoogie2Smt.getManagedScript());
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

	private Expression getExpression(final Term term, final STATE state) {
		final Map<TermVariable, String> namesMap = state.getVariables().stream()
				.filter(x -> x instanceof TemporaryBoogieVar).map(x -> (TemporaryBoogieVar) x).collect(
						Collectors.toMap(TemporaryBoogieVar::getTermVariable, TemporaryBoogieVar::getGloballyUniqueId));
		return mMappedTerm2Expression.translate(term, Collections.emptySet(), namesMap);
	}

	@Override
	public EvalResult evaluate(final STATE state, final Term term, final Script script) {
		if (state.isBottom()) {
			return EvalResult.TRUE;
		}
		final Expression expression = getExpression(term, state);
		final Collection<IEvaluationResult<V>> tmpResults = mEvaluator.evaluate(state, expression);
		boolean allTrue = true;
		boolean allFalse = true;
		for (final IEvaluationResult<V> r : tmpResults) {
			switch (r.getBooleanValue()) {
			case BOTTOM:
			case FALSE:
				allTrue = false;
				break;
			case TOP:
				allTrue = false;
				allFalse = false;
				break;
			case TRUE:
				allFalse = false;
				break;
			default:
				break;
			}
		}
		return EvalResult.selectTF(allTrue, allFalse);
	}

	/**
	 * Sets the {@link AbsIntBenchmark} for this operator.
	 *
	 * @param absIntBenchmark
	 */
	public void setAbsIntBenchmark(final AbsIntBenchmark<IcfgEdge> absIntBenchmark) {
		mAbsIntBenchmark = absIntBenchmark;
	}

	private List<STATE> handleCallTransition(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final Call call) {

		final CallStatement callStatement = call.getCallStatement();
		final CallInfo callInfo = mCallInfoCache.getCallInfo(callStatement);
		// If there are no arguments, we don't need to rewrite states.
		if (callInfo.getInParamAssign() == null) {
			return addOldvars(Collections.singletonList(stateAfterLeaving),
					callInfo.getOldVarAssign(stateAfterLeaving.getVariables()));
		}

		// process assignment of expressions in old scope to inparams of procedure
		final STATE interimState = stateBeforeLeaving.addVariables(callInfo.getTempInParams());
		final List<STATE> result = mStatementProcessor.process(interimState, callInfo.getInParamAssign(),
				callInfo.getLhs2TmpVar(), mAbsIntBenchmark);
		if (result.isEmpty()) {
			throw new AssertionError("The assignment operation resulted in 0 states.");
		}

		final List<IProgramVarOrConst> realParamVars = callInfo.getRealInParams();

		// assign values of expression evaluation to actual inparams
		final List<STATE> returnList = new ArrayList<>();
		for (final STATE resultState : result) {
			STATE returnState = stateAfterLeaving;

			for (int i = 0; i < realParamVars.size(); i++) {
				final IProgramVarOrConst tempVar = callInfo.getTempInParams().get(i);
				final IProgramVarOrConst realVar = realParamVars.get(i);

				final STATE finalReturnState = returnState;

				// TODO: Add array support.
				final Function<IProgramVarOrConst, STATE> varFunction =
						var -> finalReturnState.setValue(realVar, resultState.getValue(var));
				final Function<IProgramVarOrConst, STATE> boolFunction =
						var -> finalReturnState.setBooleanValue(realVar, resultState.getBooleanValue(tempVar));

				returnState = TypeUtils.applyVariableFunction(varFunction, boolFunction, null, tempVar);
			}

			returnList.add(returnState);
		}
		return addOldvars(new ArrayList<>(NonrelationalUtils.mergeStatesIfNecessary(returnList, mParallelStates)),
				callInfo.getOldVarAssign(stateAfterLeaving.getVariables()));
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
		final Procedure procedure = getProcedure(correspondingCall.getMethodName());
		final Pair<Deque<V>, Deque<BooleanValue>> outVals = getOutParamValues(procedure, stateBeforeLeaving);
		final VariableLHS[] lhs = correspondingCall.getLhs();

		if (outVals.getFirst().size() + outVals.getSecond().size() != lhs.length) {
			throw new UnsupportedOperationException("The expected number of return variables (" + lhs.length
					+ ") is different from the function's number of return variables (" + outVals.getFirst().size()
					+ " vals, " + outVals.getSecond().size() + " bools).");
		}

		final List<ITermProvider> inVals = getInParamValues(procedure, stateBeforeLeaving);
		final Expression[] args = correspondingCall.getArguments();

		if (inVals.size() != args.length) {
			throw new UnsupportedOperationException("The expected number of input expressions (" + args.length
					+ ") is different from the function's number of input parameters (" + inVals.size() + ").");
		}

		// Gather return variables and values for the return abstract state
		final List<IProgramVar> updateVarNames = new ArrayList<>();
		for (final VariableLHS varLhs : lhs) {
			final IProgramVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(varLhs.getIdentifier(),
					varLhs.getDeclarationInformation(), false);
			assert boogieVar != null;
			updateVarNames.add(boogieVar);
		}

		final List<Pair<IProgramVar, V>> updateVars = new ArrayList<>();
		final List<Pair<IProgramVar, BooleanValue>> updateBools = new ArrayList<>();

		// TODO: Add array support.
		final Consumer<IProgramVar> varConsumer =
				var -> updateVars.add(new Pair<>(var, outVals.getFirst().removeFirst()));
		final Consumer<IProgramVar> boolConsumer =
				var -> updateBools.add(new Pair<>(var, outVals.getSecond().removeFirst()));

		// Assign to each return variable the corresponding return value
		for (final IProgramVar boogieVar : updateVarNames) {
			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, boogieVar);
		}
		assert outVals.getFirst().isEmpty();
		assert outVals.getSecond().isEmpty();

		final List<Expression> inputParameterExpressionTerms = new ArrayList<>();

		// Update input expressions wrt. parameter values at the end of the executed procedure
		for (int i = 0; i < inVals.size(); i++) {
			final ITermProvider inValue = inVals.get(i);
			final Expression inExpression = args[i];

			final IIdentifierTranslator[] translators = new IIdentifierTranslator[] { new SimpleTranslator(),
					mBoogie2Smt.createConstOnlyIdentifierTranslator() };

			final Term expressionTerm =
					mBoogie2Smt.getExpression2Term().translateToTerm(translators, inExpression).getTerm();

			final Term valueTerm = inValue.getTerm(mBoogie2Smt.getScript(), expressionTerm.getSort(), expressionTerm);

			final Expression termExpression = mBoogie2Smt.getTerm2Expression().translate(valueTerm);

			assert termExpression.getType() == BoogieType.TYPE_BOOL;

			inputParameterExpressionTerms.add(termExpression);
		}

		final List<STATE> rets = new ArrayList<>();

		// Construct conjunction of input parameter expressions
		if (!inputParameterExpressionTerms.isEmpty()) {
			final List<STATE> postResults =
					applyInputParamExpressions(stateAfterLeaving, correspondingCall, inputParameterExpressionTerms);
			rets.addAll(postResults);
		}

		if (rets.isEmpty()) {
			rets.add(stateAfterLeaving);
		}

		// Create arrays for state update functions.
		final IProgramVar[] updateVarNameArray = updateVars.stream().map(Pair<IProgramVar, V>::getFirst)
				.collect(Collectors.toList()).toArray(new IProgramVar[updateVars.size()]);
		final V[] updateVarValsArray = updateVars.stream().map(Pair<IProgramVar, V>::getSecond)
				.collect(Collectors.toList()).toArray(stateAfterLeaving.getArray(updateVars.size()));
		final IProgramVar[] updateBoolNameArray = updateBools.stream().map(Pair<IProgramVar, BooleanValue>::getFirst)
				.collect(Collectors.toList()).toArray(new IProgramVar[updateBools.size()]);
		final BooleanValue[] updateBoolValsArray = updateBools.stream().map(Pair<IProgramVar, BooleanValue>::getSecond)
				.collect(Collectors.toList()).toArray(new BooleanValue[updateBools.size()]);

		final List<STATE> returnList = new ArrayList<>();
		for (final STATE s : rets) {
			// TODO: Implement better handling of arrays.
			returnList.add(s.setMixedValues(updateVarNameArray, updateVarValsArray, updateBoolNameArray,
					updateBoolValsArray, new IProgramVar[0], stateAfterLeaving.getArray(0)));
		}

		// add oldvars
		return new ArrayList<>(NonrelationalUtils.mergeStatesIfNecessary(returnList, mParallelStates));
	}

	private List<STATE> applyInputParamExpressions(final STATE stateAfterLeaving, final CallStatement correspondingCall,
			final List<Expression> inputParameterExpressionTerms) {
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

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    Computing post after return for arguments with statement: "
					+ BoogiePrettyPrinter.print(assume));
		}
		final List<STATE> postResults = handleInternalTransition(stateAfterLeaving, Collections.singletonList(assume));

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    Resulting post states: "
					+ postResults.stream().map(STATE::toLogString).collect(Collectors.toList()));
		}
		return postResults;
	}

	private List<STATE> handleInternalTransition(final STATE oldstate, final IcfgEdge transition) {
		final List<Statement> statements = mStatementExtractor.process(transition.getLabel());
		return handleInternalTransition(oldstate, statements);
	}

	private List<STATE> handleInternalTransition(final STATE oldstate, final List<Statement> statements) {
		List<STATE> currentStates = new ArrayList<>();
		currentStates.add(oldstate);
		for (final Statement stmt : statements) {
			final List<STATE> afterProcessStates = new ArrayList<>();
			for (final STATE currentState : currentStates) {
				final List<STATE> processed = mStatementProcessor.process(currentState, stmt, mAbsIntBenchmark);
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

		return new ArrayList<>(NonrelationalUtils.mergeStatesIfNecessary(currentStates, mParallelStates));
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
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(
					AbsIntPrefInitializer.INDENT + "Adding oldvars via " + BoogiePrettyPrinter.print(oldVarAssign));
		}
		final List<STATE> postStates = new ArrayList<>();

		for (final STATE pendingPostState : pendingPostStates) {
			postStates.addAll(mStatementProcessor.process(pendingPostState, oldVarAssign, mAbsIntBenchmark));
		}

		return new ArrayList<>(NonrelationalUtils.mergeStatesIfNecessary(postStates, mParallelStates));
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
		final Consumer<IProgramVar> varConsumer = var -> vals.add(stateBeforeLeaving.getValue(var));
		final Consumer<IProgramVar> boolConsumer = var -> boolVals.add(stateBeforeLeaving.getBooleanValue(var));

		for (final VarList list : procedure.getOutParams()) {
			for (final String s : list.getIdentifiers()) {
				final IProgramVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(s, procedure.getIdentifier(), false);
				assert boogieVar != null;
				TypeUtils.consumeVariable(varConsumer, boolConsumer, null, boogieVar);
			}
		}

		return new Pair<>(vals, boolVals);
	}

	private List<ITermProvider> getInParamValues(final Procedure procedure, final STATE stateBeforeLeaving) {
		final List<ITermProvider> vals = new ArrayList<>();

		// TODO: Add array support.
		final Consumer<IProgramVar> varConsumer = var -> vals.add(stateBeforeLeaving.getValue(var));
		final Consumer<IProgramVar> boolConsumer = var -> vals.add(stateBeforeLeaving.getBooleanValue(var));

		for (final VarList list : procedure.getInParams()) {
			for (final String s : list.getIdentifiers()) {
				final IProgramVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(s,
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
			IProgramVarOrConst var = mBoogie2SmtSymbolTable.getBoogieVar(id, declInfo, isOldContext);
			if (var == null) {
				var = mBoogie2SmtSymbolTable.getBoogieConst(id);
			}
			assert var != null : "Unknown symbol: " + id;
			return var.getTerm();
		}
	}

}
