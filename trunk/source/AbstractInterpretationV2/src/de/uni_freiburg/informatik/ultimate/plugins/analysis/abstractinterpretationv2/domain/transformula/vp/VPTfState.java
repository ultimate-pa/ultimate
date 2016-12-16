package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class VPTfState extends IVPStateOrTfState {
	
	public VPTfState(Set<VPDomainSymmetricPair<VPNodeIdentifier>> disEqs, boolean isTop, Set<IProgramVar> vars) {
		super(disEqs, isTop, vars);
		mTermToEqGraphNodeMap = null; //TODO
		mEqNodeToInVarsToOutVarsToEqGraphNode = null; // TODO
		mArrayIdToFunctionNodes = null; //TODO
	}

	private final Map<Term, TFEqGraphNode> mTermToEqGraphNodeMap;
	private final NestedMap3<EqNode, 
		Map<IProgramVar, TermVariable>, 
		Map<IProgramVar, TermVariable>, 
		TFEqGraphNode> mEqNodeToInVarsToOutVarsToEqGraphNode;
	private final HashRelation<VPArrayIdentifier, VPNodeIdentifier> mArrayIdToFunctionNodes;



	public boolean tracksTerm(Term term) {
		return mTermToEqGraphNodeMap.containsKey(term);
	}

	public boolean isBottom() {
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
	public Set<EqGraphNode> getAllEqGraphNodes() {
		return new HashSet<>(mTermToEqGraphNodeMap.values());
	}

	@Override
	public VPNodeIdentifier find(VPNodeIdentifier id) {
		return mTermToEqGraphNodeMap.get(id.getIdTerm()).find().nodeIdentifier;
	}

	public Set<VPNodeIdentifier> getFunctionNodesForArray(VPArrayIdentifier array) {
		return mArrayIdToFunctionNodes.getImage(array);
	}

}
