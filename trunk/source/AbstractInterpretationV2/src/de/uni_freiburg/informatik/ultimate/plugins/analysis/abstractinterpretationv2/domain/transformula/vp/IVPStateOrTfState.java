package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public abstract class IVPStateOrTfState {
	
	protected final Set<IProgramVar> mVars;
	private Set<VPDomainSymmetricPair<VPNodeIdentifier>> mDisEqualitySet;
	private final boolean mIsTop;
	
	public IVPStateOrTfState(
			Set<VPDomainSymmetricPair<VPNodeIdentifier>> disEqs, 
			boolean isTop, 
			Set<IProgramVar> vars) {
		mDisEqualitySet = Collections.unmodifiableSet(disEqs);
		mIsTop = isTop;
		mVars = Collections.unmodifiableSet(vars);
	}
	
	public Set<VPNodeIdentifier> getDisequalities(VPNodeIdentifier nodeIdentifer) {
		assert nodeIdentifer.getEqNode() != null;
		Set<VPNodeIdentifier> result = new HashSet<>();
		for (VPDomainSymmetricPair<VPNodeIdentifier> pair : mDisEqualitySet) {
			if (pair.contains(nodeIdentifer)) {
				result.add(pair.getOther(nodeIdentifer));
			}
		}
		return result;
	}

	public Set<VPDomainSymmetricPair<VPNodeIdentifier>> getDisEqualities() {
		return mDisEqualitySet;
	}

	abstract public boolean isBottom();

	public boolean isTop() {
		return mIsTop;
	}
	
	public Set<IProgramVar> getVariables() {
		return mVars;
	}

	/**
	 * just a convenient interface for the disequality set 
	 *  --> difference to areUnEqual: does not do a find(..) on the given nodes
	 * 
	 * @param nodeId1
	 * @param nodeId2
	 * @return
	 */
	public boolean containsDisEquality(VPNodeIdentifier nodeId1, VPNodeIdentifier nodeId2) {
		return mDisEqualitySet.contains(new VPDomainSymmetricPair<VPNodeIdentifier>(nodeId1, nodeId2));
	}	

	/**
	 * Determines if the given nodes are unequal in this state.
	 * (difference to containsDisEquality: does a find(..) on the nodes)
	 * @param nodeIdentifier1
	 * @param nodeIdentifier2
	 * @return
	 */
	public boolean areUnEqual(VPNodeIdentifier nodeIdentifier1, VPNodeIdentifier nodeIdentifier2) {
		VPNodeIdentifier find1 = find(nodeIdentifier1);
		VPNodeIdentifier find2 = find(nodeIdentifier2);
		return containsDisEquality(find1, find2);
	}
	
	public boolean areEqual(VPNodeIdentifier nodeIdentifier1, VPNodeIdentifier nodeIdentifier2) {
		VPNodeIdentifier find1 = find(nodeIdentifier1);
		VPNodeIdentifier find2 = find(nodeIdentifier2);
		return find1.equals(find2);
	}

	abstract public EqGraphNode getEqGraphNode(VPNodeIdentifier nodeIdentifier);
	
	abstract public Set<EqGraphNode> getAllEqGraphNodes();
	
	abstract public VPNodeIdentifier find(VPNodeIdentifier id);
}
