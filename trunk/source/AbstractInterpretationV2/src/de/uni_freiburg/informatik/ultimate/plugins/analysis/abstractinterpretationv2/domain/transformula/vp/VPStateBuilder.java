package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VPStateBuilder {

	private Set<IProgramVar> mVars;
	private Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;
	private Set<VPDomainSymmetricPair<EqNode>> mDisEqualitySet;
	private final VPDomain mDomain;
	private boolean mIsTop;
	
	public VPStateBuilder(VPDomain domain) {
		mDomain = domain;
	}
	
	public VPStateBuilder setVars(Set<IProgramVar> vars) { 
		mVars = vars;
		return this;
	}

	public VPStateBuilder setEqGraphNodes(Map<EqNode, EqGraphNode> map) {
		mEqNodeToEqGraphNodeMap = map;
		return this;
	}
	
	VPState build() {
		return new VPState(mEqNodeToEqGraphNodeMap, mDisEqualitySet, mVars, mDomain, mIsTop);
	}

	public VPStateBuilder setDisEqualites(Set<VPDomainSymmetricPair<EqNode>> disEqualitySet) {
		mDisEqualitySet = disEqualitySet;
		return this;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}

	public Set<VPDomainSymmetricPair<EqNode>> getDisEqualitySet() {
		return mDisEqualitySet;
	}
	
	public VPStateBuilder setIsTop(boolean b) {
		mIsTop = b;
		return this;
	}
}
