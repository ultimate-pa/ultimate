package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;

public class WrapperSideCondition {
	
	Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> mEqualities;

	Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> mDisEqualities;

}
