package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VpTfStateFactory implements IVPFactory<VPTfState>{
	
	private final VPTransFormulaStateBuilderPreparer mTfStatePreparer;

	public VpTfStateFactory(VPTransFormulaStateBuilderPreparer tfStatePreparer) {
		mTfStatePreparer = tfStatePreparer;
	}

	
	public Set<VPTfState> addEquality(Term t1, Term t2, VPTfState state) { 
		Set<VPTfState> result = VPFactoryHelpers.addEquality(
				new VPNodeIdentifier(t1), new VPNodeIdentifier(t2), state, this);
		return result;
	}
	
	public Set<VPTfState> addDisequality(Term t1, Term t2, VPTfState state) { 
		return null;
	}
	
	public Set<VPTfState> conjoin(VPTfState state1, VPTfState state2) {
		
		return null;
	}

	public VPTfState disjoin(VPTfState state1, VPTfState state2) {
		
		return null;
	}


	public Set<VPTfState> conjoinAll(List<Set<VPTfState>> andList) {
		return VPFactoryHelpers.conjoinAll(andList, this);
	}


	public VPTfState getTopState() {
		// TODO Auto-generated method stub
		return null;
	}


	public Set<VPTfState> handleArrayEqualityWithException(TermVariable newArray, Term oldArray,
			ApplicationTerm storeTerm, Term value, VPTfState tfPreState) {
		// TODO Auto-generated method stub
		return null;
	}


	public Set<VPTfState> handleArrayEquality(Term lhs, Term rhs, VPTfState tfPreState) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public VPTransitionStateBuilder copy(VPTfState state) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public VPTfState getBottomState(Set<IProgramVar> variables) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public VPTransitionStateBuilder createEmptyStateBuilder() {
		// TODO Auto-generated method stub
		return null;
	}


	public VPTfState createTfState(VPState state, UnmodifiableTransFormula tf) {
		if (state.isBottom()) {
			return getBottomState(state.getVariables());
		}
		
		if (state.isTop()) {
			VPTransitionStateBuilder builder = createEmptyStateBuilder();
			builder.addVariables(state.getVariables());
			return builder.build();
		}
	
		
		IVPStateOrTfStateBuilder<VPTfState> builder = createEmptyStateBuilder();
		builder.addVars(state.getVariables());
		builder.setIsTop(true);

		for (Entry<IProgramVar, TermVariable> inVar1 : tf.getInVars().entrySet()) {
			for (Entry<IProgramVar, TermVariable> inVar2 : tf.getInVars().entrySet()) {
				if (inVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				VPNodeIdentifier id1 = new VPNodeIdentifier(inVar1.getValue());
				VPNodeIdentifier id2 = new VPNodeIdentifier(inVar2.getValue());
				if (state.areUnEqual(id1, id2)) {
					builder.addDisEquality(id1, id2);
					builder.setIsTop(false);
				}
			}
		}
		
		VPTfState stateWithDisEqualitiesAdded = builder.build();
		
		Set<VPTfState> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);
		
		for (Entry<IProgramVar, TermVariable> inVar1 : tf.getInVars().entrySet()) {
			for (Entry<IProgramVar, TermVariable> inVar2 : tf.getInVars().entrySet()) {
				if (inVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				VPNodeIdentifier id1 = new VPNodeIdentifier(inVar1.getValue());
				VPNodeIdentifier id2 = new VPNodeIdentifier(inVar2.getValue());
				if (state.areEqual(id1, id2)) {
					resultStates = VPFactoryHelpers.addEquality(id1, id2, resultStates, this);
					builder.setIsTop(false);
				}
			}
		}
		
		assert resultStates.size() == 1 : "??";
		return resultStates.iterator().next();
	}


	@Override
	public Set<VPNodeIdentifier> getFunctionNodesForArray(VPTfState tfState, VPArrayIdentifier firstArray) {
		return tfState.getFunctionNodesForArray(firstArray);
	}	
}
