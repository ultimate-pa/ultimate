/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.CallInfoCache;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.CallInfoCache.CallInfo;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class OctPostOperator implements IAbstractPostOperator<OctDomainState, IcfgEdge> {

	private final ILogger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	private final int mMaxParallelStates;
	private final boolean mFallbackAssignIntervalProjection;

	private final HavocBundler mHavocBundler;
	private final ExpressionTransformer mExprTransformer;
	private final OctStatementProcessor mStatementProcessor;
	private final OctAssumeProcessor mAssumeProcessor;
	private final IBoogieSymbolTableVariableProvider mBpl2SmtTable;
	private final CallInfoCache mCallInfoCache;

	public OctPostOperator(final ILogger logger, final BoogieSymbolTable symbolTable, final CfgSmtToolkit cfgSmtToolkit,
			final int maxParallelStates, final boolean fallbackAssignIntervalProjection,
			final IBoogieSymbolTableVariableProvider bpl2smtSymbolTable,
			final IAbstractPostOperator<IntervalDomainState, IcfgEdge> fallBackPostOperator,
			final CodeBlockFactory codeBlockFactory) {
		if (maxParallelStates < 1) {
			throw new IllegalArgumentException("MaxParallelStates needs to be > 0, was " + maxParallelStates);
		}

		mLogger = logger;
		mSymbolTable = symbolTable;
		mBpl2SmtTable = bpl2smtSymbolTable;
		mMaxParallelStates = maxParallelStates;
		mFallbackAssignIntervalProjection = fallbackAssignIntervalProjection;

		mHavocBundler = new HavocBundler();
		mExprTransformer = new ExpressionTransformer(bpl2smtSymbolTable);
		mStatementProcessor = new OctStatementProcessor(this);
		mAssumeProcessor =
				new OctAssumeProcessor(mLogger, this, fallBackPostOperator, codeBlockFactory, bpl2smtSymbolTable);
		mCallInfoCache = new CallInfoCache(cfgSmtToolkit, symbolTable);
	}

	public static OctDomainState join(final List<OctDomainState> states) {
		OctDomainState joinedState = null;
		for (final OctDomainState result : states) {
			if (joinedState == null) {
				joinedState = result;
			} else {
				joinedState = joinedState.union(result);
			}
		}
		return joinedState;
	}

	public static List<OctDomainState> joinToSingleton(final List<OctDomainState> states) {
		return AbsIntUtil.singletonArrayList(join(states));
	}

	public static List<OctDomainState> deepCopy(final List<OctDomainState> states) {
		final List<OctDomainState> copy = new ArrayList<>(states.size());
		states.forEach(state -> copy.add(state.deepCopy()));
		return copy;
	}

	public List<OctDomainState> splitF(final List<OctDomainState> oldStates,
			final Function<List<OctDomainState>, List<OctDomainState>> op1,
			final Function<List<OctDomainState>, List<OctDomainState>> op2) {

		final List<OctDomainState> newStates = op1.apply(deepCopy(oldStates));
		newStates.addAll(op2.apply(oldStates));
		return joinDownToMax(newStates);
	}

	public List<OctDomainState> splitC(final List<OctDomainState> oldStates, final Consumer<OctDomainState> op1,
			final Consumer<OctDomainState> op2) {

		final List<OctDomainState> copiedOldStates = deepCopy(oldStates);
		oldStates.forEach(op1);
		copiedOldStates.forEach(op2);
		oldStates.addAll(copiedOldStates);
		return joinDownToMax(oldStates);
	}

	public static List<OctDomainState> removeBottomStates(final List<OctDomainState> states) {
		final List<OctDomainState> nonBottomStates = new ArrayList<>(states.size());
		for (final OctDomainState state : states) {
			if (!state.isBottom()) {
				nonBottomStates.add(state);
			}
		}
		return nonBottomStates;
	}

	public List<OctDomainState> joinDownToMax(List<OctDomainState> states) {
		if (states.size() <= mMaxParallelStates) {
			return states;
		}
		states = removeBottomStates(states);
		if (states.size() <= mMaxParallelStates) {
			return states;
		}
		return joinToSingleton(states);
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public ExpressionTransformer getExprTransformer() {
		return mExprTransformer;
	}

	public OctAssumeProcessor getAssumeProcessor() {
		return mAssumeProcessor;
	}

	public IBoogieSymbolTableVariableProvider getBoogie2SmtSymbolTable() {
		return mBpl2SmtTable;
	}

	public int getMaxParallelStates() {
		return mMaxParallelStates;
	}

	public boolean isFallbackAssignIntervalProjectionEnabled() {
		return mFallbackAssignIntervalProjection;
	}

	@Override
	public List<OctDomainState> apply(final OctDomainState oldState, final IcfgEdge edge) {
		final IcfgEdge transitionLabel = edge.getLabel();

		// TODO fix WORKAROUND unsoundness for summary code blocks without procedure implementation
		if (transitionLabel instanceof Summary && !((Summary) transitionLabel).calledProcedureHasImplementation()) {
			throw new UnsupportedOperationException("Summary for procedure without implementation");
		} else if (transitionLabel instanceof Call) {
			return applyCall(oldState, oldState, (Call) transitionLabel);
		} else if (transitionLabel instanceof Return) {
			return applyReturn(oldState, oldState, ((Return) transitionLabel).getCallStatement());
		}

		List<OctDomainState> currentState = deepCopy(Collections.singletonList(oldState));
		final List<Statement> statements = mHavocBundler.bundleHavocsCached(transitionLabel);
		for (final Statement statement : statements) {
			currentState = mStatementProcessor.processStatement(statement, currentState);
		}
		return currentState;
	}

	@Override
	public List<OctDomainState> apply(final OctDomainState stateBeforeTransition,
			final OctDomainState stateAfterTransition, final IcfgEdge transition) {

		final IcfgEdge transitionLabel = transition.getLabel();
		List<OctDomainState> result;
		if (transitionLabel instanceof Call) {
			result = applyCall(stateBeforeTransition, stateAfterTransition, (Call) transitionLabel);
		} else if (transitionLabel instanceof Return) {
			result = applyReturn(stateBeforeTransition, stateAfterTransition,
					((Return) transitionLabel).getCallStatement());
		} else if (transitionLabel instanceof Summary) {
			result = applyReturn(stateBeforeTransition, stateAfterTransition,
					((Summary) transitionLabel).getCallStatement());
		} else {
			throw new UnsupportedOperationException("Unsupported transition: " + transitionLabel);
		}
		return result;
	}

	private List<OctDomainState> applyCall(final OctDomainState stateBeforeCall, final OctDomainState stateAfterCall,
			final Call callTransition) {

		if (stateAfterCall.isBottom()) {
			return new ArrayList<>();
		}

		final CallStatement call = callTransition.getCallStatement();
		final CallInfo callInfo = mCallInfoCache.getCallInfo(call);

		List<OctDomainState> tmpStates = new ArrayList<>();
		tmpStates.add(stateBeforeCall.addVariables(callInfo.getTempInParams()));

		tmpStates = deepCopy(tmpStates);
		final AssignmentStatement invarAssign = callInfo.getInParamAssign();
		final AssignmentStatement oldvarAssign = callInfo.getOldVarAssign(stateAfterCall.getVariables());
		if (invarAssign != null) {
			for (int i = 0; i < invarAssign.getRhs().length; ++i) {
				tmpStates = mStatementProcessor.processSingleAssignment(callInfo.getTempInParams().get(i),
						invarAssign.getRhs()[i], tmpStates);
			}
		}

		if (oldvarAssign != null) {
			tmpStates = mStatementProcessor.processStatement(oldvarAssign, tmpStates);
		}

		// inParam := tmp (copy to scope opened by call)
		// note: bottom-states are not overwritten (see top of this method)
		final List<OctDomainState> result = new ArrayList<>();

		tmpStates.forEach(
				s -> result.add(stateAfterCall.copyValuesOnScopeChange(s, callInfo.getInParam2TmpVars(), true)));
		return result;
		// No need to remove the temporary variables.
		// The states with temporary variables are only local variables of this method.
	}

	private List<OctDomainState> applyReturn(final OctDomainState stateBeforeReturn, OctDomainState stateAfterReturn,
			final CallStatement correspondingCall) {

		final ArrayList<OctDomainState> result = new ArrayList<>();
		if (!stateAfterReturn.isBottom()) {
			final Procedure procedure = calledProcedure(correspondingCall);
			final List<Pair<IProgramVarOrConst, IProgramVarOrConst>> mapLhsToOut =
					generateMapCallLhsToOutParams(correspondingCall.getLhs(), procedure);
			stateAfterReturn = stateAfterReturn.copyValuesOnScopeChange(stateBeforeReturn, mapLhsToOut, false);
			result.add(stateAfterReturn);
		}
		return result;
	}

	private Procedure calledProcedure(final CallStatement call) {
		final List<Declaration> procedureDeclarations =
				mSymbolTable.getFunctionOrProcedureDeclaration(call.getMethodName());
		Procedure implementation = null;
		for (final Declaration d : procedureDeclarations) {
			assert d instanceof Procedure : "call/return of non-procedure " + call.getMethodName() + ": " + d;
			final Procedure p = (Procedure) d;
			if (p.getBody() != null) {
				if (implementation != null) {
					throw new UnsupportedOperationException("Multiple implementations of " + call.getMethodName());
				}
				implementation = p;
			}
		}
		if (implementation == null) {
			throw new UnsupportedOperationException("Missing implementation of " + call.getMethodName());
		}
		return implementation;
	}

	private List<Pair<IProgramVarOrConst, IProgramVarOrConst>>
			generateMapCallLhsToOutParams(final VariableLHS[] callLhs, final Procedure calledProcedure) {
		final List<Pair<IProgramVarOrConst, IProgramVarOrConst>> mapLhsToOut = new ArrayList<>(callLhs.length);
		int i = 0;
		for (final VarList outParamList : calledProcedure.getOutParams()) {
			for (final String outParam : outParamList.getIdentifiers()) {
				assert i < callLhs.length : "missing left hand side for out-parameter";
				final VariableLHS currentLhs = callLhs[i];
				final IProgramVar lhsBoogieVar = mBpl2SmtTable.getBoogieVar(currentLhs.getIdentifier(),
						currentLhs.getDeclarationInformation(), false);
				assert lhsBoogieVar != null;
				final IProgramVar outParamBoogieVar =
						mBpl2SmtTable.getBoogieVar(outParam, calledProcedure.getIdentifier(), false);
				assert outParamBoogieVar != null;
				mapLhsToOut.add(new Pair<>(lhsBoogieVar, outParamBoogieVar));
				++i;
			}
		}
		assert i == callLhs.length : "missing out-parameter for left hand side";
		return mapLhsToOut;
	}

	IProgramVar getBoogieVar(final VariableLHS vLhs) {
		IProgramVar rtr =
				getBoogie2SmtSymbolTable().getBoogieVar(vLhs.getIdentifier(), vLhs.getDeclarationInformation(), false);
		if (rtr == null) {
			// hack for oldvars
			final String newIdent = vLhs.getIdentifier().replaceAll("old\\((.*)\\)", "$1");
			rtr = getBoogie2SmtSymbolTable().getBoogieVar(newIdent, vLhs.getDeclarationInformation(), false);
			rtr = ((BoogieNonOldVar) rtr).getOldVar();
		}
		assert rtr != null : "Unknown Boogie var: " + vLhs.getIdentifier();
		return rtr;
	}

	IProgramVarOrConst getBoogieVar(final IdentifierExpression ie) {
		IProgramVarOrConst returnVar =
				getBoogie2SmtSymbolTable().getBoogieVar(ie.getIdentifier(), ie.getDeclarationInformation(), false);
		if (returnVar != null) {
			return returnVar;
		}

		returnVar = getBoogie2SmtSymbolTable().getBoogieConst(ie.getIdentifier());
		assert returnVar != null;
		return returnVar;
	}

	@Override
	public EvalResult evaluate(final OctDomainState state, final Term formula, final Script script) {
		return state.evaluate(script, formula);
	}

}
