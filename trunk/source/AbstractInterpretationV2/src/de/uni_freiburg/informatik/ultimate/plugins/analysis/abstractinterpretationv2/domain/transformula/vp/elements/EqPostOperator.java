package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;

public class EqPostOperator<ACTION extends IIcfgTransition<IcfgLocation>> implements
		IAbstractPostOperator<
			AbstractMultiState<EqConstraint<ACTION, EqNode, EqFunction>, IProgramVarOrConst>, 
			ACTION, 
			IProgramVarOrConst> {
	
	private ManagedScript mScript;
	private EqOperationProvider<ACTION> operationProvider;

	@Override
	public List<AbstractMultiState<EqConstraint<ACTION, EqNode, EqFunction>, IProgramVarOrConst>> apply(
			AbstractMultiState<EqConstraint<ACTION, EqNode, EqFunction>, IProgramVarOrConst> oldstate,
			ACTION transition) {
		
		EqTransitionRelation<ACTION> transrel = null;

		PredicateTransformer<
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>, 
			EqPredicate<ACTION>, 
			EqTransitionRelation<ACTION>> pt = new PredicateTransformer<>(mScript, operationProvider);	

		return Collections.singletonList(
				pt.strongestPostcondition(
						new EqPredicate<ACTION>((EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>) oldstate), 
							transrel));
	}

	@Override
	public List<AbstractMultiState<EqConstraint<ACTION, EqNode, EqFunction>, IProgramVarOrConst>> apply(
			AbstractMultiState<EqConstraint<ACTION, EqNode, EqFunction>, IProgramVarOrConst> stateBeforeLeaving,
			AbstractMultiState<EqConstraint<ACTION, EqNode, EqFunction>, IProgramVarOrConst> stateAfterLeaving,
			ACTION transition) {
		
//		PredicateTransformer<
//			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>, 
//			EqPredicate<ACTION>, 
//			EqTransitionRelation<ACTION>> pt = new PredicateTransformer<>(mScript, operationProvider);	
//
//		pt.strongestPostconditionReturn(returnPred, callPred, returnTF, callTF, oldVarAssignments, modifiableGlobals)

		
		// TODO Auto-generated method stub
		return null;
	}

	
}
