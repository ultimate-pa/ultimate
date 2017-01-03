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
	
}
