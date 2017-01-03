package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;

public class UndetermindedNodeWithSideCondition extends NodeIdWithSideCondition {

	public UndetermindedNodeWithSideCondition(
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> equalities,
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqualities) {
		super(null, equalities, disEqualities);
	}

	@Override
	public VPTfNodeIdentifier getNodeId() {
		assert false : "check if it is an undetermined node before calling this";
		return null;
	}
}
