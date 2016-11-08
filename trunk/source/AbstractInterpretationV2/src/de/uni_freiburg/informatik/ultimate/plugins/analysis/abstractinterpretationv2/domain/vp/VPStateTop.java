package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
*
* @author Yu-Wen Chen (yuwenchen1105@gmail.com)
*
*/
public class VPStateTop extends VPState {
	
	VPStateTop(Set<EqGraphNode> eqGraphNodeSet, Map<Term, EqBaseNode> termToBaseNodeMap,
			Map<Term, Set<EqFunctionNode>> termToFnNodeMap, Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap,
			Set<VPDomainSymmetricPair<EqNode>> disEqualitySet, VPStateBottom bottomState) {
		super(eqGraphNodeSet, termToBaseNodeMap, termToFnNodeMap, eqNodeToEqGraphNodeMap, disEqualitySet, bottomState);
		this.clearState();
	}
	
	@Override
	public boolean isBottom() {
		// A basic dataflow state is never bottom
		return false;
	}

	@Override
	public VPState prepareState(Set<IProgramVar> assignmentVars) {
		// Do nothing
		return this;
	}

	@Override
	public VPState conjoin(VPState state1, VPState state2) {
		// Do nothing
		return this;
	}

	@Override
	public VPState disjoin(VPState state1, VPState state2) {
		// Do nothing
		return this;
	}

	@Override
	public boolean addEquality(EqNode node1, EqNode node2) {
		// Do nothing
		return true;
	}

	@Override
	public boolean addDisEquality(EqNode node1, EqNode node2) {
		// Do nothing
		return true;
	}

	@Override
	public VPState addVariable(IProgramVar variable) {
		// Do nothing
		return this;
	}

	@Override
	public VPState removeVariable(IProgramVar variable) {
		// Do nothing
		return this;
	}

	@Override
	public VPState addVariables(Collection<IProgramVar> variables) {
		// Do nothing
		return this;
	}

	@Override
	public VPState removeVariables(Collection<IProgramVar> variables) {
		// Do nothing
		return this;
	}

	@Override
	public VPState copy() {
		return super.copy();
	}

	@Override
	public boolean containsVariable(IProgramVar var) {
		// Do nothing
		return false;
	}

	@Override
	public Set<IProgramVar> getVariables() {
		// Do nothing
		return null;
	}

	@Override
	public VPState patch(VPState dominator) {
		// Auto-generated method stub
		return super.patch(dominator);
	}

	@Override
	public boolean isEmpty() {
		// Auto-generated method stub
		return super.isEmpty();
	}

	@Override
	public boolean isEqualTo(VPState other) {
		// Auto-generated method stub
		return super.isEqualTo(other);
	}

	@Override
	public SubsetResult isSubsetOf(
			VPState other) {
		// Auto-generated method stub
		return super.isSubsetOf(other);
	}

	@Override
	public String toLogString() {
		
		return "Top state.";
	}

	@Override
	public boolean equals(Object obj) {
		// Auto-generated method stub
		return super.equals(obj);
	}

	@Override
	VPState union(VPState other) {
		// Auto-generated method stub
		return super.union(other);
	}
	
}
