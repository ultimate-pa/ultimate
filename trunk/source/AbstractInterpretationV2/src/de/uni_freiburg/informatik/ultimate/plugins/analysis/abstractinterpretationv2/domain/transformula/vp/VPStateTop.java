package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

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
	
	VPStateTop(Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap,
			Set<VPDomainSymmetricPair<EqGraphNode>> disEqualitySet, VPDomain domain) {
		super(eqNodeToEqGraphNodeMap, disEqualitySet, domain);
		this.clearState();
	}
	
	@Override
	public boolean isBottom() {
		return false;
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
	
}
