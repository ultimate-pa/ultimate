package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class VPTfState implements IVPStateOrTfState{
	
	Map<Term, TFEqGraphNode> mTermToEqGraphNodeMap;
	private NestedMap3<EqNode, 
		Map<IProgramVar, TermVariable>, 
		Map<IProgramVar, TermVariable>, 
		TFEqGraphNode> mEqNodeToInVarsToOutVarsToEqGraphNode;



	public boolean tracksTerm(Term param1) {
		// TODO Auto-generated method stub
		return false;
	}

	public boolean isBottom() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<VPDomainSymmetricPair<VPNodeIdentifier>> getDisEqualities() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isTop() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<IProgramVar> getVariables() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean containsDisEquality(VPNodeIdentifier nodeIdentifier, VPNodeIdentifier nodeIdentifier2) {
		// TODO Auto-generated method stub
		return false;
	}

	public EqGraphNode getEqGraphNode(Term term) {
		TFEqGraphNode result = mTermToEqGraphNodeMap.get(term);
		assert result != null;
		return result;
	}

	@Override
	public EqGraphNode getEqGraphNode(VPNodeIdentifier nodeIdentifier) {
		return getEqGraphNode(nodeIdentifier.getIdTerm());
	}

	@Override
	public Set<VPNodeIdentifier> getDisequalities(VPNodeIdentifier nodeIdentifer) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<EqGraphNode> getAllEqGraphNodes() {
		return new HashSet<>(mTermToEqGraphNodeMap.values());
	}

}
