package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public abstract class IVPStateOrTfState<NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> {
	
	protected final Set<IProgramVar> mVars;
	private Set<VPDomainSymmetricPair<NODEID>> mDisEqualitySet;
	private final boolean mIsTop;
	
	public IVPStateOrTfState(
			Set<VPDomainSymmetricPair<NODEID>> disEqs, 
			boolean isTop, 
			Set<IProgramVar> vars) {
		mDisEqualitySet = Collections.unmodifiableSet(disEqs);
		mIsTop = isTop;
		mVars = Collections.unmodifiableSet(vars);
	}
	
	public Set<NODEID> getDisequalities(NODEID nodeIdentifer) {
//		assert nodeIdentifer.getEqNode() != null;
		Set<NODEID> result = new HashSet<>();
		for (VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (pair.contains(nodeIdentifer)) {
				result.add(pair.getOther(nodeIdentifer));
			}
		}
		return result;
	}

	public Set<VPDomainSymmetricPair<NODEID>> getDisEqualities() {
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
	public boolean containsDisEquality(NODEID nodeId1, NODEID nodeId2) {
		return mDisEqualitySet.contains(new VPDomainSymmetricPair<NODEID>(nodeId1, nodeId2));
	}	

	/**
	 * Determines if the given nodes are unequal in this state.
	 * (difference to containsDisEquality: does a find(..) on the nodes)
	 * @param nodeIdentifier1
	 * @param nodeIdentifier2
	 * @return
	 */
	public boolean areUnEqual(NODEID nodeIdentifier1, NODEID nodeIdentifier2) {
		NODEID find1 = find(nodeIdentifier1);
		NODEID find2 = find(nodeIdentifier2);
		return containsDisEquality(find1, find2);
	}
	
	public boolean areEqual(NODEID nodeIdentifier1, NODEID nodeIdentifier2) {
		NODEID find1 = find(nodeIdentifier1);
		NODEID find2 = find(nodeIdentifier2);
		return find1.equals(find2);
	}

	abstract public EqGraphNode<NODEID, ARRAYID> getEqGraphNode(NODEID nodeIdentifier);
	
	abstract public Set<EqGraphNode<NODEID, ARRAYID>> getAllEqGraphNodes();
	
	abstract public NODEID find(NODEID id);
}
