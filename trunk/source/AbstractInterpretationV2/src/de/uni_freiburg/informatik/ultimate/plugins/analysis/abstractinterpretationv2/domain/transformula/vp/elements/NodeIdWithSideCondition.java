package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;

public class NodeIdWithSideCondition implements INodeOrArrayWithSideCondition {
	
	final VPTfNodeIdentifier mNodeId;
	
	final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> mEqualities;

	final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> mDisEqualities;

	public NodeIdWithSideCondition(VPTfNodeIdentifier nodeId,
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> equalities,
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqualities) {
		this.mNodeId = nodeId;
		this.mEqualities = equalities;
		this.mDisEqualities = disEqualities;
	}

	public VPTfNodeIdentifier getNodeId() {
		return mNodeId;
	}

	public Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> getEqualities() {
		return mEqualities;
	}

	public Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> getDisEqualities() {
		return mDisEqualities;
	}
	
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		sb.append("NodeIdWithSideCondition: ");
		
		sb.append(mNodeId);

		//sb.append("\n");
		
		String sep = "";
		
		for (VPDomainSymmetricPair<VPTfNodeIdentifier> eq : mEqualities) {
			sb.append(sep);
			sb.append(eq.getFirst().getEqNode() + "=" + eq.getSecond().getEqNode());
			sep = ", ";
		}

		for (VPDomainSymmetricPair<VPTfNodeIdentifier> deq : mDisEqualities) {
			sb.append(sep);
			sb.append(deq.getFirst().getEqNode() + "!=" + deq.getSecond().getEqNode());
			sep = ", ";
		}
		
		return sb.toString();
	}
}
