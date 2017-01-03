package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;

public interface INodeOrArrayWithSideCondition {

	public Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> getEqualities();

	public Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> getDisEqualities();
}
