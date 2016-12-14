package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

public class VpTfStateFactory {
	
	private final VPTransFormulaStateBuilderPreparer mTfStatePreparer;

	public VpTfStateFactory(VPTransFormulaStateBuilderPreparer tfStatePreparer) {
		mTfStatePreparer = tfStatePreparer;
	}

	
	public Set<VPTfState> addEquality(Term t1, Term t2, VPTfState state) { 
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


	public Set<VPTfState> conjoinAll(Set<VPTfState>... transitionStateSets) {
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
}
