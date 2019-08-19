/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.statistics.BenchmarkWithCounters;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param
 */
public class EqPostOperator<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractPostOperator<EqState, ACTION> {

	private final ManagedScript mMgdScript;

	private final PredicateTransformer<EqDisjunctiveConstraint<EqNode>, EqPredicate, EqTransitionRelation> mPredicateTransformer;

	/**
	 * used for sanity/soundness checks only
	 */
	private final PredicateTransformer<Term, IPredicate, TransFormula> mDoubleCheckPredicateTransformer;
	private final MonolithicImplicationChecker mDoubleCheckImplicationChecker;

	private final TransFormulaConverterCache mTransFormulaConverter;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final EqConstraintFactory<EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;

	private final boolean mDebug = true;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final EqStateFactory mEqStateFactory;

	private final VPDomainSettings mSettings;

	private final BenchmarkWithCounters mBenchmark;

	public EqPostOperator(final IUltimateServiceProvider services, final ILogger logger, final CfgSmtToolkit csToolkit,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory,
			final EqConstraintFactory<EqNode> eqConstraintFactory, final EqStateFactory eqStateFactory,
			final VPDomainSettings settings) {
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
		mCfgSmtToolkit = csToolkit;
		mMgdScript = csToolkit.getManagedScript();
		mEqStateFactory = eqStateFactory;

		mSettings = settings;

		mServices = services;
		mLogger = logger;

		mPredicateTransformer = new PredicateTransformer<>(mMgdScript, new EqOperationProvider(eqConstraintFactory));
		mTransFormulaConverter = new TransFormulaConverterCache(mServices, mMgdScript, mEqNodeAndFunctionFactory,
				mEqConstraintFactory, mSettings);
		mEqStateFactory.registerTransformulaConverter(mTransFormulaConverter);

		mDoubleCheckPredicateTransformer =
				new PredicateTransformer<>(mMgdScript, new TermDomainOperationProvider(mServices, mMgdScript));
		mDoubleCheckImplicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);

		if (mDebug) {
			mBenchmark = new BenchmarkWithCounters();
			mBenchmark.registerCountersAndWatches(BmNames.getNames());
		} else {
			mBenchmark = null;
		}
	}

	@Override
	public List<EqState> apply(final EqState oldState, final ACTION transition) {
		debugStart(BmNames.APPLY_NORMAL);
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			// timeout
			debugEnd(BmNames.APPLY_NORMAL);
			return toEqStates(mEqConstraintFactory.getEmptyDisjunctiveConstraint(false), oldState.getVariables());
		}

		final EqTransitionRelation transitionRelation =
				mTransFormulaConverter.getOrConstructEqTransitionRelationFromTransformula(transition.getTransformula());

		final EqDisjunctiveConstraint<EqNode> postConstraint =
				mPredicateTransformer.strongestPostcondition(oldState.toEqPredicate(), transitionRelation);
		final List<EqState> result = toEqStates(postConstraint, oldState.getVariables());
		assert result.stream().allMatch(state -> state.getVariables().containsAll(oldState.getVariables()));
		if (mDebug && mSettings.isCheckPostCorrectness()) {
			mLogger.debug(postConstraint.getDebugInfo());
			assert preciseStrongestPostImpliesAbstractPost(oldState, transition,
					mEqStateFactory.statesToPredicate(result)) : "soundness check failed!";
		}
		// TransFormulaUtils.prettyPrint(transition.getTransformula())
		debugEnd(BmNames.APPLY_NORMAL);
		return result;
	}

	/**
	 * Convert an EqDisjunctiveConstraints to a corresponding set of EqStates. (Assumes that all the TermVariables and
	 * nullary ApplicationTerms in this.mConstraints have a symbol table entry.)
	 *
	 * @param variablesThatTheFrameworkLikesToSee
	 * @return
	 */
	private List<EqState> toEqStates(final EqDisjunctiveConstraint<EqNode> disjunctiveConstraint,
			final Set<IProgramVarOrConst> variablesThatTheFrameworkLikesToSee) {
		/*
		 * The AbstractInterpretation framework demands that all EqStates here have the same Pvocs Thus we set the Pvocs
		 * of all the disjunct-states to be the union of the pvocs that each disjunct-state/constraint talks about.
		 * EDIT: the variables are now determined externally (by the oldstate of the post operator..)
		 */
		return disjunctiveConstraint.getConstraints().stream()
				.map(cons -> mEqStateFactory.getEqState(cons, variablesThatTheFrameworkLikesToSee))
				.collect(Collectors.toList());
	}

	private boolean preciseStrongestPostImpliesAbstractPost(final EqState oldState, final ACTION transition,
			final IPredicate postConstraint) {

		final Term spPrecise = mDoubleCheckPredicateTransformer.strongestPostcondition(oldState.toEqPredicate(),
				transition.getTransformula());
		final EqPredicate spPred = mEqStateFactory.termToPredicate(spPrecise, postConstraint);

		final Validity icRes = mDoubleCheckImplicationChecker.checkImplication(spPred, false, postConstraint, false);
		assert icRes != Validity.INVALID : "soundness check failed!";
		return icRes != Validity.INVALID;
	}

	@Override
	public List<EqState> apply(final EqState stateBeforeLeaving, final EqState hierarchicalPrestate,
			final ACTION transition) {
		// DD: You should not require having all variables of the current scope, only variables occuring in the
		// transition are necessary
		// assert hierarchicalPrestate.getVariables()
		// .containsAll(mCfgSmtToolkit.getSymbolTable().getGlobals());
		// assert hierarchicalPrestate.getVariables()
		// .containsAll(mCfgSmtToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure()));
		debugStart(BmNames.APPLY_RETURN);

		if (!mServices.getProgressMonitorService().continueProcessing()) {
			// timeout
			debugEnd(BmNames.APPLY_RETURN);
			return toEqStates(mEqConstraintFactory.getEmptyDisjunctiveConstraint(false),
					hierarchicalPrestate.getVariables());
		}

		if (transition instanceof ICallAction) {
			final String calledProcedure = transition.getSucceedingProcedure();

			final EqTransitionRelation localVarAssignments =
					mTransFormulaConverter.getOrConstructEqTransitionRelationFromTransformula(
							((ICallAction) transition).getLocalVarsAssignment());
			final EqTransitionRelation globalVarAssignments =
					mTransFormulaConverter.getOrConstructEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProcedure));
			final EqTransitionRelation oldVarAssignments =
					mTransFormulaConverter.getOrConstructEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProcedure));

			final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure =
					mCfgSmtToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProcedure);

			final EqDisjunctiveConstraint<EqNode> postConstraint = mPredicateTransformer.strongestPostconditionCall(
					stateBeforeLeaving.toEqPredicate(), localVarAssignments, globalVarAssignments, oldVarAssignments,
					modifiableGlobalsOfCalledProcedure);
			// TODO implement SMT solver soundness check (like in other apply method)
			final List<EqState> result = toEqStates(postConstraint, hierarchicalPrestate.getVariables());
			debugEnd(BmNames.APPLY_RETURN);
			return result;
		} else if (transition instanceof IReturnAction) {

			final EqPredicate returnPred = stateBeforeLeaving.toEqPredicate();

			final Set<IProgramVar> oldVars =
					hierarchicalPrestate.getConstraint().getVariables(mCfgSmtToolkit.getSymbolTable()).stream()
							.filter(var -> var.isOldvar()).collect(Collectors.toSet());
			final Set<Term> ovTvs = oldVars.stream().map(ov -> ov.getTermVariable()).collect(Collectors.toSet());
			final EqConstraint<EqNode> projectedCons =
					mEqConstraintFactory.projectExistentially(ovTvs, hierarchicalPrestate.getConstraint(), false);
			final EqState hier = mEqStateFactory.getEqState(projectedCons, hierarchicalPrestate.getVariables());

			final EqPredicate callPred = hier.toEqPredicate();

			final EqTransitionRelation returnTF =
					mTransFormulaConverter.getOrConstructEqTransitionRelationFromTransformula(
							((IReturnAction) transition).getAssignmentOfReturn());
			final EqTransitionRelation callTF =
					mTransFormulaConverter.getOrConstructEqTransitionRelationFromTransformula(
							((IReturnAction) transition).getLocalVarsAssignmentOfCall());
			final EqTransitionRelation oldVarAssignments =
					mTransFormulaConverter.getOrConstructEqTransitionRelationFromTransformula(mCfgSmtToolkit
							.getOldVarsAssignmentCache().getOldVarsAssignment(transition.getPrecedingProcedure()));
			final Set<IProgramNonOldVar> modifiableGlobals = mCfgSmtToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(transition.getPrecedingProcedure());

			final EqDisjunctiveConstraint<EqNode> postConstraint = mPredicateTransformer.strongestPostconditionReturn(
					returnPred, callPred, returnTF, callTF, oldVarAssignments, modifiableGlobals);

			// TODO implement SMT solver soundness check (like in other apply method)
			final List<EqState> result = toEqStates(postConstraint, hierarchicalPrestate.getVariables());
			debugEnd(BmNames.APPLY_RETURN);
			return result;
		} else {
			debugEnd(BmNames.APPLY_RETURN);
			throw new UnsupportedOperationException();
		}
	}

	public TransFormulaConverterCache getTransformulaConverterCache() {
		return mTransFormulaConverter;
	}

	public BenchmarkWithCounters getBenchmark() {
		return mBenchmark;
	}

	private void debugStart(final BmNames name) {
		if (mDebug) {
			mBenchmark.incrementCounter(name.name());
			mBenchmark.unpauseWatch(name.name());
		}
	}

	private void debugEnd(final BmNames name) {
		if (mDebug) {
			mBenchmark.pauseWatch(name.name());
		}
	}

	private static enum BmNames {

		APPLY_NORMAL, APPLY_RETURN;

		static String[] getNames() {
			final String[] result = new String[values().length];
			for (int i = 0; i < values().length; i++) {
				result[i] = values()[i].name();
			}
			return result;
		}
	}

	@Override
	public EvalResult evaluate(final EqState state, final Term formula, final Script script) {
		throw new UnsupportedOperationException("Not implemented yet.");
	}
}
