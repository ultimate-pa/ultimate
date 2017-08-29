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

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
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
public class EqPostOperator<ACTION extends IIcfgTransition<IcfgLocation>> implements
		IAbstractPostOperator<EqState<ACTION>, ACTION, IProgramVarOrConst> {

	private final ManagedScript mMgdScript;
	private final EqOperationProvider<ACTION> mOperationProvider;

	private final PredicateTransformer<
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>,
			EqPredicate<ACTION>,
			EqTransitionRelation<ACTION>> mPredicateTransformer;
	private final TransFormulaConverterCache<ACTION> mTransFormulaConverter;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final VPDomainPreanalysis mPreAnalysis;

	public EqPostOperator(final EqNodeAndFunctionFactory eqNodeAndFunctionFactory,
			final EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory,
			final VPDomainPreanalysis preAnalysis) {
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
		mPreAnalysis = preAnalysis;
		mMgdScript = preAnalysis.getManagedScript();
		mCfgSmtToolkit = preAnalysis.getCfgSmtToolkit();

		mOperationProvider = new EqOperationProvider<>(eqConstraintFactory);

		mPredicateTransformer = new PredicateTransformer<>(mMgdScript, mOperationProvider);
		mTransFormulaConverter = new TransFormulaConverterCache<>(mEqNodeAndFunctionFactory,
				mEqConstraintFactory, mPreAnalysis);
	}

	@Override
	public List<EqState<ACTION>> apply(final EqState<ACTION> oldstate, final ACTION transition) {
		if (!mPreAnalysis.getServices().getProgressMonitorService().continueProcessing()) {
			return mEqConstraintFactory.getTopDisjunctiveConstraint().toEqStates(oldstate.getVariables());
		}

		final EqTransitionRelation<ACTION> transitionRelation =
				mTransFormulaConverter.getEqTransitionRelationFromTransformula(transition.getTransformula());

		final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> postConstraint =
				mPredicateTransformer.strongestPostcondition(
						oldstate.toEqPredicate(), transitionRelation);
		final List<EqState<ACTION>> result = postConstraint.toEqStates(oldstate.getVariables());
		assert result.stream().allMatch(state -> state.getVariables().containsAll(oldstate.getVariables()));
		return result;
	}

	@Override
	public List<EqState<ACTION>> apply(final EqState<ACTION> stateBeforeLeaving,
			final EqState<ACTION> hierarchicalPreOrStateAfterLeaving,
			final ACTION transition) {
		assert hierarchicalPreOrStateAfterLeaving.getVariables().containsAll(
				mCfgSmtToolkit.getSymbolTable().getGlobals());
		assert hierarchicalPreOrStateAfterLeaving.getVariables().containsAll(
				mCfgSmtToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure()));

		if (!mPreAnalysis.getServices().getProgressMonitorService().continueProcessing()) {
			return mEqConstraintFactory.getTopDisjunctiveConstraint()
					.toEqStates(hierarchicalPreOrStateAfterLeaving.getVariables());
		}

		if (transition instanceof ICallAction) {
			final String calledProcedure = transition.getSucceedingProcedure();

			final EqTransitionRelation<ACTION> localVarAssignments = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(((ICallAction) transition)
							.getLocalVarsAssignment());
			final EqTransitionRelation<ACTION> globalVarAssignments = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProcedure));
			final EqTransitionRelation<ACTION> oldVarAssignments = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProcedure));

			final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure =
							mCfgSmtToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProcedure);

			final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> postConstraint =
					mPredicateTransformer.strongestPostconditionCall(
							stateBeforeLeaving.toEqPredicate(),
							localVarAssignments, globalVarAssignments, oldVarAssignments,
							modifiableGlobalsOfCalledProcedure);
			final List<EqState<ACTION>> result =
					postConstraint.toEqStates(hierarchicalPreOrStateAfterLeaving.getVariables());
			return result;
		} else if (transition instanceof IReturnAction) {

			final EqPredicate<ACTION> returnPred = stateBeforeLeaving.toEqPredicate();

			final Set<IProgramVar> oldVars =
					hierarchicalPreOrStateAfterLeaving.getConstraint().getVariables(
							mCfgSmtToolkit.getSymbolTable()).stream().filter(var -> var.isOldvar()).collect(Collectors.toSet());
			final Set<TermVariable> ovTvs = oldVars.stream().map(ov -> ov.getTermVariable()).collect(Collectors.toSet());
			final EqConstraint<ACTION, EqNode, EqFunction> projectedCons =
					mEqConstraintFactory.projectExistentially(ovTvs,
							hierarchicalPreOrStateAfterLeaving.getConstraint());
			final EqState<ACTION> hier = mEqConstraintFactory.getEqStateFactory()
					.getEqState(projectedCons, hierarchicalPreOrStateAfterLeaving.getVariables());

			final EqPredicate<ACTION> callPred = hier.toEqPredicate();

			final EqTransitionRelation<ACTION> returnTF = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(((IReturnAction) transition).getAssignmentOfReturn());
			final EqTransitionRelation<ACTION> callTF = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(
							((IReturnAction) transition).getLocalVarsAssignmentOfCall());
			final EqTransitionRelation<ACTION> oldVarAssignments = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(
									transition.getPrecedingProcedure()));
			final Set<IProgramNonOldVar> modifiableGlobals = mCfgSmtToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(transition.getPrecedingProcedure());

			final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> postConstraint =
					mPredicateTransformer.strongestPostconditionReturn(returnPred,
							callPred,
							returnTF,
							callTF,
							oldVarAssignments,
							modifiableGlobals);

			final List<EqState<ACTION>> result =
					postConstraint.toEqStates(hierarchicalPreOrStateAfterLeaving.getVariables());
//			assert result.stream()
//				.allMatch(state -> state.getVariables().containsAll(hierarchicalPreOrStateAfterLeaving.getVariables()));
			return result;
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
