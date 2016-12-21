package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class VPTfState extends IVPStateOrTfState<VPNodeIdentifier, VPArrayIdentifier> {
	
	private Map<Term, VPNodeIdentifier> mTermToNodeId;



//	public VPTfState(
//			TransFormula tf,
//			Map<Term, EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> termToEqGraphNodeMap,
//			HashRelation<VPArrayIdentifier, VPNodeIdentifier> arrayIdToFunctionNodes,
//			Set<VPDomainSymmetricPair<VPNodeIdentifier>> disEqs, 
//			boolean isTop, 
//			Set<IProgramVar> vars) {
//		super(disEqs, isTop, vars);
//		mTransFormula = tf;
//		mTermToEqGraphNodeMap = Collections.unmodifiableMap(termToEqGraphNodeMap);
//		mEqNodeToInVarsToOutVarsToEqGraphNode = null; // TODO
//		mArrayIdToFunctionNodes = arrayIdToFunctionNodes;
//	}

	public VPTfState(TransFormula tf,
			Map<VPNodeIdentifier, EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> nodeIdToEqGraphNode,
			Map<Term, VPNodeIdentifier> termToNodeId,
			HashRelation<VPArrayIdentifier, VPNodeIdentifier> arrayIdToFunctionNodes,
			Set<VPDomainSymmetricPair<VPNodeIdentifier>> disEqs, 
			boolean isTop, 
			Set<IProgramVar> vars) {
		super(disEqs, isTop, vars);
		mTransFormula = tf;
		mTermToNodeId = termToNodeId;
		mNodeIdToEqGraphNode = nodeIdToEqGraphNode;
		mArrayIdToFunctionNodes = arrayIdToFunctionNodes;
	}

	private final TransFormula mTransFormula;
//	private final Map<Term, EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> mTermToEqGraphNodeMap;
//	private final NestedMap3<EqNode, 
//		Map<IProgramVar, TermVariable>, 
//		Map<IProgramVar, TermVariable>, 
//		EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> mEqNodeToInVarsToOutVarsToEqGraphNode;
	private final HashRelation<VPArrayIdentifier, VPNodeIdentifier> mArrayIdToFunctionNodes;
	private Map<VPNodeIdentifier, EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> mNodeIdToEqGraphNode = new HashMap<>();



	public boolean tracksTerm(Term term) {
		return mTermToNodeId.containsKey(term);
	}

	public boolean isBottom() {
		return false;
	}

//	public EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> getEqGraphNode(Term term) {
//		EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> result = mTermToEqGraphNodeMap.get(term);
//		assert result != null;
//		return result;
//	}

	@Override
	public EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> getEqGraphNode(VPNodeIdentifier nodeIdentifier) {
//		return getEqGraphNode(nodeIdentifier.getIdTerm());
		return mNodeIdToEqGraphNode.get(nodeIdentifier);
	}

	@Override
	public Set<EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> getAllEqGraphNodes() {
		return new HashSet<>(mNodeIdToEqGraphNode.values());
	}

	@Override
	public VPNodeIdentifier find(VPNodeIdentifier id) {
		return mNodeIdToEqGraphNode.get(id).find().nodeIdentifier;
	}

	public Set<VPNodeIdentifier> getFunctionNodesForArray(VPArrayIdentifier array) {
		return mArrayIdToFunctionNodes.getImage(array);
	}

	public TransFormula getTransFormula() {
		return mTransFormula;
	}
	
	public VPNodeIdentifier getNodeId(Term t) {
		return mTermToNodeId.get(t);
	}
}
