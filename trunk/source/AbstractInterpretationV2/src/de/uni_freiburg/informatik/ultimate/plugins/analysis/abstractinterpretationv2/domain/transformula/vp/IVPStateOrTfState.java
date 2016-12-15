package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public interface IVPStateOrTfState {

	public Set<VPDomainSymmetricPair<VPNodeIdentifier>> getDisEqualities();
	
	
	public boolean isBottom();

	public boolean isTop();
	
	public Set<IProgramVar> getVariables();

	public boolean containsDisEquality(VPNodeIdentifier nodeIdentifier, VPNodeIdentifier nodeIdentifier2);
	
	public EqGraphNode getEqGraphNode(VPNodeIdentifier nodeIdentifier);
	
	public Set<VPNodeIdentifier> getDisequalities(VPNodeIdentifier nodeIdentifer);
	
	public Set<EqGraphNode> getAllEqGraphNodes();
	
	public VPNodeIdentifier find(VPNodeIdentifier id);
}
