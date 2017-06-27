package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.TransFormulaConverterCache;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

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
	
	public EqPostOperator(EqNodeAndFunctionFactory eqNodeAndFunctionFactory, 
			EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory, 
			VPDomainPreanalysis preAnalysis) {
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
		mPreAnalysis = preAnalysis;
		mMgdScript = preAnalysis.getManagedScript();
		mCfgSmtToolkit = preAnalysis.getCfgSmtToolkit();

		mOperationProvider = new EqOperationProvider<>(eqConstraintFactory);

		mPredicateTransformer = new PredicateTransformer<>(mMgdScript, mOperationProvider);	
		mTransFormulaConverter = new TransFormulaConverterCache<ACTION>(mEqNodeAndFunctionFactory, 
				mEqConstraintFactory, mPreAnalysis);
	}

	@Override
	public List<EqState<ACTION>> apply(EqState<ACTION> oldstate, ACTION transition) {
		
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
	public List<EqState<ACTION>> apply(EqState<ACTION> stateBeforeLeaving, 
			EqState<ACTION> hierarchicalPreOrStateAfterLeaving,
			ACTION transition) {
		assert hierarchicalPreOrStateAfterLeaving.getVariables().containsAll(
				mCfgSmtToolkit.getSymbolTable().getGlobals());
		assert hierarchicalPreOrStateAfterLeaving.getVariables().containsAll(
				mCfgSmtToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure()));

		if (transition instanceof Call) {
			final String calledProcedure = transition.getSucceedingProcedure();

			final EqTransitionRelation<ACTION> localVarAssignments = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(((Call) transition)
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
			//TODO where do we get the variables for the new scope??
//			Set<ILocalProgramVar> newScopeLocalVars = 
//					mCfgSmtToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure());
//			Set<IProgramNonOldVar> globalVars = mCfgSmtToolkit.getSymbolTable().getGlobals();
//			Set<IProgramConst> constants = mCfgSmtToolkit.getSymbolTable().getConstants();
//			Set<IProgramVarOrConst> newScopePvocs = new HashSet<>();
//			newScopePvocs.addAll(newScopeLocalVars);
//			newScopePvocs.addAll(globalVars);
//			newScopePvocs.addAll(constants);
//			return postConstraint.toEqStates(newScopePvocs); 
			final List<EqState<ACTION>> result = 
					postConstraint.toEqStates(hierarchicalPreOrStateAfterLeaving.getVariables()); 
			assert result.stream()
				.allMatch(state -> state.getVariables().containsAll(hierarchicalPreOrStateAfterLeaving.getVariables()));
			return result;
		} else if (transition instanceof Summary) {
			return apply(stateBeforeLeaving, transition);
		} else if (transition instanceof Return) {

			final EqPredicate<ACTION> returnPred = stateBeforeLeaving.toEqPredicate();
			final EqPredicate<ACTION> callPred = hierarchicalPreOrStateAfterLeaving.toEqPredicate();

			EqTransitionRelation<ACTION> returnTF = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(((Return) transition).getAssignmentOfReturn());
			EqTransitionRelation<ACTION> callTF = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(
							((Return) transition).getLocalVarsAssignmentOfCall());
			EqTransitionRelation<ACTION> oldVarAssignments = mTransFormulaConverter
					.getEqTransitionRelationFromTransformula(
							mCfgSmtToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(
									transition.getPrecedingProcedure()));
			Set<IProgramNonOldVar> modifiableGlobals = mCfgSmtToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(transition.getPrecedingProcedure());

			final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> postConstraint = 
					mPredicateTransformer.strongestPostconditionReturn(returnPred, 
							callPred, 
							returnTF, 
							callTF, 
							oldVarAssignments, 
							modifiableGlobals);
			
//			Set<ILocalProgramVar> newScopeLocalVars = 
//					mCfgSmtToolkit.getSymbolTable().getLocals(transition.getSucceedingProcedure());
//			Set<IProgramNonOldVar> globalVars = mCfgSmtToolkit.getSymbolTable().getGlobals();
//			Set<IProgramConst> constants = mCfgSmtToolkit.getSymbolTable().getConstants();
//			Set<IProgramVarOrConst> newScopePvocs = new HashSet<>();
//			newScopePvocs.addAll(newScopeLocalVars);
//			newScopePvocs.addAll(globalVars);
//			newScopePvocs.addAll(constants);
//			return postConstraint.toEqStates(newScopePvocs); 
			
			final List<EqState<ACTION>> result = 
					postConstraint.toEqStates(hierarchicalPreOrStateAfterLeaving.getVariables());
			assert result.stream()
				.allMatch(state -> state.getVariables().containsAll(hierarchicalPreOrStateAfterLeaving.getVariables()));
			return result;
		} else {
			throw new UnsupportedOperationException();
		}
	}

//	/**
//	 * copied with minimal modifications from AbstractMultiState..
//	 * used only for assertions
//	 * @param states
//	 * @return
//	 */
//	private boolean haveSameVars(final Collection<EqState<ACTION>> states) {
//		if (states.size() <= 1) {
//			return true;
//		}
//		final Set<IProgramVarOrConst> firstVars = states.iterator().next().getVariables();
//		return states.stream().allMatch(a -> firstVars.equals(a.getVariables()));
//	}
	
}
