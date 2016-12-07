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
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ITermProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The post operator of the interval domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class NonrelationalPostOperator<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		implements IAbstractPostOperator<STATE, CodeBlock, IBoogieVar> {
	
	private final ILogger mLogger;
	private final RcfgStatementExtractor mStatementExtractor;
	private final NonrelationalStatementProcessor<STATE, V> mStatementProcessor;
	private final BoogieSymbolTable mSymbolTable;
	private final int mParallelStates;
	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	private final Boogie2SMT mBoogie2Smt;
	private final BoogieIcfgContainer mRootAnnotation;
	
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
	}
	
	@Override
	public List<STATE> apply(final STATE oldstate, final CodeBlock transition) {
		assert oldstate != null;
		assert !oldstate.isBottom() : "You should not need to calculate post of a bottom state";
		assert transition != null;
		
		List<STATE> currentStates = new ArrayList<>();
		currentStates.add(oldstate);
		final List<Statement> statements = mStatementExtractor.process(transition);
		
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
	
	@Override
	public List<STATE> apply(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final CodeBlock transition) {
		assert transition instanceof Call || transition instanceof Return
				|| transition instanceof Summary : "Cannot calculate hierachical post for non-hierachical transition";
		
		if (transition instanceof Call) {
			final Call call = (Call) transition;
			return handleCallTransition(stateBeforeLeaving, stateAfterLeaving, call);
		} else if (transition instanceof Return) {
			final Return ret = (Return) transition;
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, ret.getCallStatement());
		} else if (transition instanceof Summary) {
			final Summary summary = (Summary) transition;
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, summary.getCallStatement());
		} else {
			throw new UnsupportedOperationException(
					"Nonrelational domains do not support context switches other than Call and Return (yet)");
		}
	}
	
	private List<STATE> handleCallTransition(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final Call call) {
		final List<STATE> returnList = new ArrayList<>();
		final CallStatement callStatement = call.getCallStatement();
		final Expression[] args = callStatement.getArguments();
		
		// If there are no arguments, we don't need to rewrite states.
		if (args.length == 0) {
			returnList.add(stateAfterLeaving);
			return returnList;
		}
		
		final Map<Integer, String> tmpParamNames = getArgumentTemporaries(args.length, stateBeforeLeaving);
		final List<LeftHandSide> idents = new ArrayList<>();
		final Map<LeftHandSide, IBoogieVar> tmpVarUses = new HashMap<>();
		final Map<String, IBoogieVar> tmpParamVars = new HashMap<>();
		final ILocation loc = callStatement.getLocation();
		for (int i = 0; i < args.length; i++) {
			final String name = tmpParamNames.get(i);
			final IBoogieVar boogieVar = BoogieUtil.createTemporaryIBoogieVar(name, args[i].getType());
			final VariableLHS lhs = new VariableLHS(loc, name);
			tmpParamVars.put(name, boogieVar);
			tmpVarUses.put(lhs, boogieVar);
			idents.add(lhs);
		}
		
		final AssignmentStatement assign = new AssignmentStatement(callStatement.getLocation(),
				idents.toArray(new LeftHandSide[idents.size()]), args);
		final STATE interimState = stateBeforeLeaving.addVariables(tmpParamVars.values());
		final List<STATE> result = mStatementProcessor.process(interimState, assign, tmpVarUses);
		if (result.isEmpty()) {
			throw new UnsupportedOperationException("The assingment operation resulted in 0 states.");
		}
		
		final Procedure procedure = getProcedure(callStatement.getMethodName());
		assert procedure != null;
		final VarList[] inParams = procedure.getInParams();
		final List<IBoogieVar> realParamVars = new ArrayList<>();
		
		for (final VarList varlist : inParams) {
			for (final String var : varlist.getIdentifiers()) {
				final IBoogieVar bVar = mBoogie2SmtSymbolTable.getBoogieVar(var, callStatement.getMethodName(), true);
				assert bVar != null;
				realParamVars.add(bVar);
			}
		}
		
		if (args.length != realParamVars.size()) {
			throw new UnsupportedOperationException(
					"The number of the expressions in the call statement arguments does not correspond to the length of the number of arguments in the symbol table.");
		}
		
		for (final STATE resultState : result) {
			STATE returnState = stateAfterLeaving.createCopy();
			
			for (int i = 0; i < realParamVars.size(); i++) {
				final String tempName = tmpParamNames.get(i);
				final IBoogieVar realVar = realParamVars.get(i);
				final IBoogieVar tempVar = tmpParamVars.get(tempName);
				
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
		
		return NonrelationalUtils.mergeStatesIfNecessary(returnList, mParallelStates);
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
			final CallStatement correspondingCall) {
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
			
			final CodeBlock newPostBlock = mRootAnnotation.getCodeBlockFactory().constructStatementSequence(null, null,
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
	private Map<Integer, String> getArgumentTemporaries(final int argNum, final STATE state) {
		final Map<Integer, String> returnMap = new HashMap<>();
		
		String paramPrefix = "param_";
		final Set<String> varNames =
				state.getVariables().stream().map(a -> a.getGloballyUniqueId()).collect(Collectors.toSet());
		boolean uniqueFound = false;
		
		while (!uniqueFound) {
			for (int i = 0; i < argNum; i++) {
				final StringBuilder sb = new StringBuilder();
				sb.append(paramPrefix).append(i);
				final String currentParamName = sb.toString();
				if (varNames.contains(currentParamName)) {
					final StringBuilder paramBuilder = new StringBuilder();
					paramBuilder.append(paramPrefix).append('_');
					paramPrefix = paramBuilder.toString();
					break;
				}
			}
			uniqueFound = true;
		}
		
		for (int i = 0; i < argNum; i++) {
			final StringBuilder sb = new StringBuilder();
			sb.append(paramPrefix).append(i);
			returnMap.put(i, sb.toString());
		}
		
		return returnMap;
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
			final BoogieVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(id, declInfo, isOldContext);
			assert boogieVar != null;
			return boogieVar.getTermVariable();
		}
	}
}
