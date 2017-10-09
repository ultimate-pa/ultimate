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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.TransFormulaConverterCache;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class EqPostOperator<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractPostOperator<EqState<ACTION>, ACTION> {

	private final ManagedScript mMgdScript;

	private final PredicateTransformer<
		EqDisjunctiveConstraint<ACTION, EqNode>,
		EqPredicate<ACTION>,
		EqTransitionRelation<ACTION>> mPredicateTransformer;

	/**
	 * used for sanity/soundness checks only
	 */
	private final PredicateTransformer<Term, IPredicate, TransFormula> mDoubleCheckPredicateTransformer;
	private final MonolithicImplicationChecker mDoubleCheckImplicationChecker;

	private final TransFormulaConverterCache<ACTION> mTransFormulaConverter;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final EqConstraintFactory<ACTION, EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final VPDomainPreanalysis mPreAnalysis;

	private final boolean mDebug = true;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public EqPostOperator(final IUltimateServiceProvider services, final ILogger logger,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory,
			final EqConstraintFactory<ACTION, EqNode> eqConstraintFactory, final VPDomainPreanalysis preAnalysis) {
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
		mPreAnalysis = preAnalysis;
		mMgdScript = preAnalysis.getManagedScript();
		mCfgSmtToolkit = preAnalysis.getCfgSmtToolkit();

		mServices = services;
		mLogger = logger;

		mPredicateTransformer = new PredicateTransformer<>(mMgdScript,new EqOperationProvider<>(eqConstraintFactory));
		mTransFormulaConverter =
				new TransFormulaConverterCache<>(mServices, mMgdScript, mEqNodeAndFunctionFactory,
						mEqConstraintFactory);


		mDoubleCheckPredicateTransformer = new PredicateTransformer<>(mMgdScript,
				new TermDomainOperationProvider(mServices, mMgdScript));
		mDoubleCheckImplicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);
	}

	@Override
	public List<EqState<ACTION>> apply(final EqState<ACTION> oldState, final ACTION transition) {
		if (!mPreAnalysis.getServices().getProgressMonitorService().continueProcessing()) {
			return mEqConstraintFactory.getTopDisjunctiveConstraint().toEqStates(oldState.getVariables());
		}

		final EqTransitionRelation<ACTION> transitionRelation =
				mTransFormulaConverter.getEqTransitionRelationFromTransformula(transition.getTransformula());

		final EqDisjunctiveConstraint<ACTION, EqNode> postConstraint =
				mPredicateTransformer.strongestPostcondition(oldState.toEqPredicate(), transitionRelation);
		final List<EqState<ACTION>> result = postConstraint.toEqStates(oldState.getVariables());
		assert result.stream().allMatch(state -> state.getVariables().containsAll(oldState.getVariables()));
		if (mDebug) {
			mLogger.debug(postConstraint.getDebugInfo());
			assert preciseStrongestPostImpliesAbstractPost(oldState, transition,
					mEqConstraintFactory.getEqStateFactory().statesToPredicate(result)) : "soundness check failed!";
		}
		return result;
	}

	private boolean preciseStrongestPostImpliesAbstractPost(final EqState<ACTION> oldState, final ACTION transition,
			final IPredicate postConstraint) {

		final Term spPrecise = mDoubleCheckPredicateTransformer.strongestPostcondition(oldState.toEqPredicate(),
				transition.getTransformula());
		final EqPredicate<IIcfgTransition<IcfgLocation>> spPred =
				mEqConstraintFactory.getEqStateFactory().termToPredicate(spPrecise, postConstraint);

		final Validity icRes = mDoubleCheckImplicationChecker.checkImplication(spPred, false, postConstraint, false);
		assert icRes != Validity.INVALID : "soundness check failed!";
		return icRes != Validity.INVALID;
	}

	@Override
	public List<EqState<ACTION>> apply(final EqState<ACTION> stateBeforeLeaving,
			final EqState<ACTION> hierarchicalPrestate, final ACTION transition) {
		assert hierarchicalPrestate.getVariables()
				.containsAll(mCfgSmtToolkit.getSymbolTable().getGlobals());
		assert hierarchicalPrestate.getVariables()
				.containsAll(mCfgSmtToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure()));

		if (!mPreAnalysis.getServices().getProgressMonitorService().continueProcessing()) {
			return mEqConstraintFactory.getTopDisjunctiveConstraint()
					.toEqStates(hierarchicalPrestate.getVariables());
		}

		if (transition instanceof ICallAction) {
			final String calledProcedure = transition.getSucceedingProcedure();

			final EqTransitionRelation<ACTION> localVarAssignments = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(((ICallAction) transition).getLocalVarsAssignment());
			final EqTransitionRelation<ACTION> globalVarAssignments =
					mTransFormulaConverter.getEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProcedure));
			final EqTransitionRelation<ACTION> oldVarAssignments =
					mTransFormulaConverter.getEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProcedure));

			final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure =
					mCfgSmtToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProcedure);

			final EqDisjunctiveConstraint<ACTION, EqNode> postConstraint = mPredicateTransformer
					.strongestPostconditionCall(stateBeforeLeaving.toEqPredicate(), localVarAssignments,
							globalVarAssignments, oldVarAssignments, modifiableGlobalsOfCalledProcedure);
			final List<EqState<ACTION>> result =
					postConstraint.toEqStates(hierarchicalPrestate.getVariables());
			return result;
		} else if (transition instanceof IReturnAction) {

			final EqPredicate<ACTION> returnPred = stateBeforeLeaving.toEqPredicate();

			final Set<IProgramVar> oldVars =
					hierarchicalPrestate.getConstraint().getVariables(mCfgSmtToolkit.getSymbolTable())
							.stream().filter(var -> var.isOldvar()).collect(Collectors.toSet());
			final Set<TermVariable> ovTvs =
					oldVars.stream().map(ov -> ov.getTermVariable()).collect(Collectors.toSet());
			final EqConstraint<ACTION, EqNode> projectedCons = mEqConstraintFactory.projectExistentially(ovTvs,
					hierarchicalPrestate.getConstraint());
			final EqState<ACTION> hier = mEqConstraintFactory.getEqStateFactory().getEqState(projectedCons,
					hierarchicalPrestate.getVariables());

			final EqPredicate<ACTION> callPred = hier.toEqPredicate();

			final EqTransitionRelation<ACTION> returnTF = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(((IReturnAction) transition).getAssignmentOfReturn());
			final EqTransitionRelation<ACTION> callTF = mTransFormulaConverter.getEqTransitionRelationFromTransformula(
					((IReturnAction) transition).getLocalVarsAssignmentOfCall());
			final EqTransitionRelation<ACTION> oldVarAssignments =
					mTransFormulaConverter.getEqTransitionRelationFromTransformula(mCfgSmtToolkit
							.getOldVarsAssignmentCache().getOldVarsAssignment(transition.getPrecedingProcedure()));
			final Set<IProgramNonOldVar> modifiableGlobals = mCfgSmtToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(transition.getPrecedingProcedure());

			final EqDisjunctiveConstraint<ACTION, EqNode> postConstraint =
					mPredicateTransformer.strongestPostconditionReturn(returnPred, callPred, returnTF, callTF,
							oldVarAssignments, modifiableGlobals);

			final List<EqState<ACTION>> result =
					postConstraint.toEqStates(hierarchicalPrestate.getVariables());
			return result;
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
