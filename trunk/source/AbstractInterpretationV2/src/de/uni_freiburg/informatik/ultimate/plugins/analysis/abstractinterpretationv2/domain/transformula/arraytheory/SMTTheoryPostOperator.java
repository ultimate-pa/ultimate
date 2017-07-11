package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;

public class SMTTheoryPostOperator implements IAbstractPostOperator<SMTTheoryState, IcfgEdge, IProgramVarOrConst> {
	
	private SMTTheoryTransitionRelationProvider mTransitionRelationProvider;
	private PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	private SMTTheoryStateFactoryAndPredicateHelper mStateFactory;
	private SMTTheoryOperationProvider mArrayTheoryOperationProvider;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final IUltimateServiceProvider mServices;
	
	public SMTTheoryPostOperator(IUltimateServiceProvider services, CfgSmtToolkit csToolkit) {
		mServices = services;
		mCfgSmtToolkit = csToolkit;
		mArrayTheoryOperationProvider = new SMTTheoryOperationProvider(services, csToolkit.getManagedScript());
		mPredicateTransformer = new PredicateTransformer<>(csToolkit.getManagedScript(), mArrayTheoryOperationProvider);
		mTransitionRelationProvider = new SMTTheoryTransitionRelationProvider(services, csToolkit.getManagedScript());
		mStateFactory = new SMTTheoryStateFactoryAndPredicateHelper(services, csToolkit, 
				mArrayTheoryOperationProvider);
		
	}

	@Override
	public List<SMTTheoryState> apply(SMTTheoryState oldstate, IcfgEdge transition) {
		
		final Set<TransFormula> transRels = mTransitionRelationProvider.getTransitionRelationDNF(transition);

		final List<SMTTheoryState> result = new ArrayList<>();
		for (TransFormula transRel : transRels) {
			final Term resTerm = mPredicateTransformer.strongestPostcondition(oldstate.getPredicate(), transRel);
			
//			final Term conjunction = dropQuantifiedConjuncts(resTerm);
//			
//			result.add(mStateFactory.getOrConstructState(conjunction, oldstate.getVariables()));
			result.add(mStateFactory.getOrConstructState(resTerm, oldstate.getVariables()));
		}
		
		return result;
	}

	private Term dropQuantifiedConjuncts(final Term resTerm) {
		final List<Term> filteredConjuncts = Arrays.stream(SmtUtils.getConjuncts(resTerm))
				.filter(conjunct -> (!(conjunct instanceof QuantifiedFormula)))
				.collect(Collectors.toList());
		final Term conjunction = SmtUtils.and(mCfgSmtToolkit.getManagedScript().getScript(), filteredConjuncts);
		return conjunction;
	}

	@Override
	public List<SMTTheoryState> apply(SMTTheoryState stateBeforeLeaving, 
			SMTTheoryState hierarchicalPreOrStateAfterLeaving,
			IcfgEdge transition) {
		
		assert hierarchicalPreOrStateAfterLeaving.getVariables().containsAll(
				mCfgSmtToolkit.getSymbolTable().getGlobals());
		assert hierarchicalPreOrStateAfterLeaving.getVariables().containsAll(
				mCfgSmtToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure()));

		if (!mServices.getProgressMonitorService().continueProcessing()) {
			return Collections.singletonList(mStateFactory.getTopState());
		}

		if (transition instanceof ICallAction) {
			final String calledProcedure = transition.getSucceedingProcedure();

			final UnmodifiableTransFormula localVarAssignments = ((ICallAction) transition).getLocalVarsAssignment();
			final UnmodifiableTransFormula globalVarAssignments = 
							mCfgSmtToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProcedure);
			final UnmodifiableTransFormula oldVarAssignments = 
					mCfgSmtToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProcedure);
			final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure = 
							mCfgSmtToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProcedure);
			
			// TOOD assert all tfs are conjunctive and only contain equalities

			final Term postConstraint = mPredicateTransformer.strongestPostconditionCall(
					stateBeforeLeaving.getPredicate(), 
					localVarAssignments, globalVarAssignments, oldVarAssignments, 
					modifiableGlobalsOfCalledProcedure);
			return Collections.singletonList(mStateFactory.getOrConstructState(postConstraint, 
					hierarchicalPreOrStateAfterLeaving.getVariables()));
		} else if (transition instanceof IReturnAction) {
			final Set<IProgramVar> oldVars = 
					hierarchicalPreOrStateAfterLeaving.getVariables().stream()
							.filter(var -> (var instanceof IProgramVar) && ((IProgramVar) var).isOldvar())
							.map(var -> (IProgramVar) var)
							.collect(Collectors.toSet());
			final Set<TermVariable> ovTvs = oldVars.stream().map(ov -> ov.getTermVariable()).collect(Collectors.toSet());
			final Term projectedCons = 
					mArrayTheoryOperationProvider.projectExistentially(ovTvs, 
							hierarchicalPreOrStateAfterLeaving.getPredicate().getFormula());
			final SMTTheoryState callPred = mStateFactory.getOrConstructState(projectedCons, 
					hierarchicalPreOrStateAfterLeaving.getVariables());

			final UnmodifiableTransFormula returnTF = ((IReturnAction) transition).getAssignmentOfReturn();
			final UnmodifiableTransFormula callTF = ((IReturnAction) transition).getLocalVarsAssignmentOfCall();
			final UnmodifiableTransFormula oldVarAssignments = mCfgSmtToolkit.getOldVarsAssignmentCache()
					.getOldVarsAssignment(transition.getPrecedingProcedure());
			final Set<IProgramNonOldVar> modifiableGlobals = mCfgSmtToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(transition.getPrecedingProcedure());

			// TOOD assert all tfs are conjunctive and only contain equalities

			 final Term postConstraint = mPredicateTransformer.strongestPostconditionReturn(
					 stateBeforeLeaving.getPredicate(), 
					callPred.getPredicate(), 
					returnTF, 
					callTF, 
					oldVarAssignments, 
					modifiableGlobals);
			
			return Collections.singletonList(mStateFactory.getOrConstructState(postConstraint, 
					hierarchicalPreOrStateAfterLeaving.getVariables()));
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public  SMTTheoryStateFactoryAndPredicateHelper getStateFactory() {
		return mStateFactory;
	}

}
