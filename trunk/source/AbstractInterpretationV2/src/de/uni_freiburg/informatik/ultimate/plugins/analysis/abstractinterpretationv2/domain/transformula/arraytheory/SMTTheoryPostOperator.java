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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.DnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class SMTTheoryPostOperator implements IAbstractPostOperator<SMTTheoryState, IcfgEdge> {

	private final SMTTheoryTransitionRelationProvider mTransitionRelationProvider;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	private final SMTTheoryStateFactoryAndPredicateHelper mStateFactory;
	private final SMTTheoryOperationProvider mArrayTheoryOperationProvider;
	private final CfgSmtToolkit mCsToolkit;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;

	public SMTTheoryPostOperator(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit) {
		mServices = services;
		mCsToolkit = csToolkit;
		mLogger = services.getLoggingService().getLogger(getClass());
		mMgdScript = csToolkit.getManagedScript();

		mArrayTheoryOperationProvider = new SMTTheoryOperationProvider(services, csToolkit);
		mPredicateTransformer = new PredicateTransformer<>(csToolkit.getManagedScript(), mArrayTheoryOperationProvider);
		mTransitionRelationProvider = new SMTTheoryTransitionRelationProvider(services, csToolkit.getManagedScript());
		mStateFactory = new SMTTheoryStateFactoryAndPredicateHelper(services, csToolkit, mArrayTheoryOperationProvider);

	}

	@Override
	public List<SMTTheoryState> apply(final SMTTheoryState oldstate, final IcfgEdge transition) {

		final Set<TransFormula> transRels = mTransitionRelationProvider.getTransitionRelationDNF(transition);

		final List<SMTTheoryState> result = new ArrayList<>();
		for (final TransFormula transRel : transRels) {
			final Term resTerm = mPredicateTransformer.strongestPostcondition(oldstate.getPredicate(), transRel);

			final List<Term> postProcessed = postProcessStrongestPost(resTerm);

			;

			result.addAll(
					postProcessed.stream().map(term -> mStateFactory.getOrConstructState(term, oldstate.getVariables()))
							.collect(Collectors.toList()));
			// result.add();
		}

		return result;
	}

	private List<Term> postProcessStrongestPost(final Term term) {

		final Term eliminated = PartialQuantifierElimination.tryToEliminate(mServices, mLogger,
				mCsToolkit.getManagedScript(), term, SimplificationTechnique.SIMPLIFY_QUICK,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		// final Term conjunction = dropQuantifiedConjuncts(resTerm);

		// partial quantifier elimination may introduce disjunctions --> convert to DNF
		final List<Term> dnfDisjuncts =
				Arrays.asList(SmtUtils.getDisjuncts(new DnfTransformer(mMgdScript, mServices).transform(eliminated)));

		return dnfDisjuncts;
	}

	// TODO: unclear if this is useful/necessary
	private Term dropQuantifiedConjuncts(final Term resTerm) {
		final List<Term> filteredConjuncts = Arrays.stream(SmtUtils.getConjuncts(resTerm))
				.filter(conjunct -> !(conjunct instanceof QuantifiedFormula)).collect(Collectors.toList());
		final Term conjunction = SmtUtils.and(mCsToolkit.getManagedScript().getScript(), filteredConjuncts);
		return conjunction;
	}

	@Override
	public List<SMTTheoryState> apply(final SMTTheoryState stateBeforeLeaving,
			final SMTTheoryState hierarchicalPreOrStateAfterLeaving, final IcfgEdge transition) {

		assert hierarchicalPreOrStateAfterLeaving.getVariables().containsAll(mCsToolkit.getSymbolTable().getGlobals());
		assert hierarchicalPreOrStateAfterLeaving.getVariables()
				.containsAll(mCsToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure()));

		if (!mServices.getProgressMonitorService().continueProcessing()) {
			return Collections.singletonList(mStateFactory.getTopState());
		}

		if (transition instanceof ICallAction) {
			final String calledProcedure = transition.getSucceedingProcedure();

			final UnmodifiableTransFormula localVarAssignments = ((ICallAction) transition).getLocalVarsAssignment();
			final UnmodifiableTransFormula globalVarAssignments =
					mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProcedure);
			final UnmodifiableTransFormula oldVarAssignments =
					mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProcedure);
			final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure =
					mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProcedure);

			// TOOD assert all tfs are conjunctive and only contain equalities

			final Term postConstraint = mPredicateTransformer.strongestPostconditionCall(
					stateBeforeLeaving.getPredicate(), localVarAssignments, globalVarAssignments, oldVarAssignments,
					modifiableGlobalsOfCalledProcedure);
			return Collections.singletonList(mStateFactory.getOrConstructState(postConstraint,
					hierarchicalPreOrStateAfterLeaving.getVariables()));
		} else if (transition instanceof IReturnAction) {
			// the hierarchicalPrestate may contain oldVars in its predicate --> we need to project them out
			final Set<IProgramVar> oldVars = hierarchicalPreOrStateAfterLeaving.getPredicate().getVars().stream()
					.filter(var -> var instanceof IProgramVar && var.isOldvar()).map(var -> var)
					.collect(Collectors.toSet());
			final Set<TermVariable> ovTvs =
					oldVars.stream().map(ov -> ov.getTermVariable()).collect(Collectors.toSet());
			final Term projectedCons = mArrayTheoryOperationProvider.projectExistentially(ovTvs,
					hierarchicalPreOrStateAfterLeaving.getPredicate().getFormula());
			final SMTTheoryState callPred =
					mStateFactory.getOrConstructState(projectedCons, hierarchicalPreOrStateAfterLeaving.getVariables());

			// retrieve all the necessary transformulas
			final UnmodifiableTransFormula returnTF = ((IReturnAction) transition).getTransformula();// .getAssignmentOfReturn();
			final UnmodifiableTransFormula callTF = ((IReturnAction) transition).getLocalVarsAssignmentOfCall();
			final UnmodifiableTransFormula oldVarAssignments =
					mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(transition.getPrecedingProcedure());
			final Set<IProgramNonOldVar> modifiableGlobals =
					mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(transition.getPrecedingProcedure());

			// TOOD assert all tfs are conjunctive and only contain equalities

			final Term postConstraint =
					mPredicateTransformer.strongestPostconditionReturn(stateBeforeLeaving.getPredicate(),
							callPred.getPredicate(), returnTF, callTF, oldVarAssignments, modifiableGlobals);

			final List<SMTTheoryState> res = Collections.singletonList(mStateFactory.getOrConstructState(postConstraint,
					hierarchicalPreOrStateAfterLeaving.getVariables()));
			return res;
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public SMTTheoryStateFactoryAndPredicateHelper getStateFactory() {
		return mStateFactory;
	}

	@Override
	public EvalResult evaluate(final SMTTheoryState state, final Term formula, final Script script) {
		throw new UnsupportedOperationException("Not implemented yet.");
	}

}
