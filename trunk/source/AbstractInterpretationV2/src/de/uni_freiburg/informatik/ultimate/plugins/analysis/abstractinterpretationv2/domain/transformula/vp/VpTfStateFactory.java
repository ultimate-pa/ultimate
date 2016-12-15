package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.List;
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
		state.getEqGraphNode(nodeIdentifier)
	}
	
	private VPTransitionStateBuilder copy(VPTfState state) {
		// TODO Auto-generated method stub
		return null;
	}


	public Set<VPTfState> addDisequality(Term t1, Term t2, VPTfState state) { 
		return null;
	}
	
	public VPTfState havoc(VPTfState state) {
		return null;
	}

	public Set<VPTfState> conjoin(VPTfState state1, VPTfState state2) {
		
		return null;
	}

	public VPTfState disjoin(VPTfState state1, VPTfState state2) {
		
		return null;
	}


	public VPTfState createTfState(VPState oldState, UnmodifiableTransFormula tf) {
		// TODO Auto-generated method stub
		return null;
	}


	public Set<VPTfState> conjoinAll(List<Set<VPTfState>> andList) {
		// TODO Auto-generated method stub
		return null;
	}


	public VPTfState getBottomState() {
		// TODO Auto-generated method stub
		return null;
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
	public IVPStateOrTfStateBuilder<VPTfState> copy(VPTfState state) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public VPTfState getBottomState(Set<IProgramVar> variables) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public IVPStateOrTfStateBuilder<VPTfState> createEmptyStateBuilder() {
		// TODO Auto-generated method stub
		return null;
	}	
}
