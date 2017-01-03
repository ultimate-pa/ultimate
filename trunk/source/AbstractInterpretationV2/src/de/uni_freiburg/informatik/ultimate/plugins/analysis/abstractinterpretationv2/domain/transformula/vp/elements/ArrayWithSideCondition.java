package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;

/**
 * Represents an "anonymous array" (like a lambda function is an anonymous function) together
 * with a set of equalities and a set of disequalities.
 * Those sets represent sideconditions under which the represented array is to be used.
 * 
 * @author Alexander Nutz
 */
public class ArrayWithSideCondition implements INodeOrArrayWithSideCondition {

	/**
	 * stores for each index that is constrained on this array the value it has in this array
	 */
	final Map<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> mIndexToValue;
	
	final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> mEqualities;

	final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> mDisEqualities;

	public ArrayWithSideCondition(Map<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> indexToValue,
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> equalities,
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqualities) {
		this.mIndexToValue = indexToValue;
		this.mEqualities = equalities;
		this.mDisEqualities = disEqualities;
	}

	@Override
	public Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> getEqualities() {
		return mEqualities;
	}

	@Override
	public Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> getDisEqualities() {
		return mDisEqualities;
	}
	
	public Map<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> getIndexToValue() {
		return mIndexToValue;
	}
	
	
}
