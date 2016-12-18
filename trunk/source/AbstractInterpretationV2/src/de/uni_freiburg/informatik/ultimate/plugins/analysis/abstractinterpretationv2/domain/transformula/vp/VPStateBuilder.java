package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class VPStateBuilder<ACTION extends IIcfgTransition<IcfgLocation>>
		extends IVPStateOrTfStateBuilder<VPState<ACTION>> {

	protected Set<IProgramVar> mVars;
	protected final VPDomain<ACTION> mDomain;
	protected boolean mIsTop;
	protected EqGraph mEqGraph;

	private Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;

	public VPStateBuilder(final VPDomain<ACTION> domain) {
		mDomain = domain;
		mEqGraph = new EqGraph();
		createEqGraphNodes();
		mVars = new HashSet<>();
	}

	protected VPStateBuilder(final VPDomain<ACTION> domain, final boolean dontCreateEqGraphNodes) {
		assert dontCreateEqGraphNodes;
		mDomain = domain;
		mEqGraph = new EqGraph();
		mVars = new HashSet<>();
	}

	private void createEqGraphNodes() {
		/*
		 * Create fresh EqGraphNodes from EqNodes.
		 */
		final Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap = new HashMap<>();
		for (final EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			getOrConstructEqGraphNode(eqNode, eqNodeToEqGraphNodeMap);
		}
		mEqNodeToEqGraphNodeMap = Collections.unmodifiableMap(eqNodeToEqGraphNodeMap);
	}

	private EqGraphNode getOrConstructEqGraphNode(final EqNode eqNode,
			final Map<EqNode, EqGraphNode> eqNodeToEqGraphNode) {

		if (eqNodeToEqGraphNode.containsKey(eqNode)) {
			return eqNodeToEqGraphNode.get(eqNode);
		}

		final EqGraphNode graphNode = new EqGraphNode(eqNode);
		final List<EqGraphNode> argNodes = new ArrayList<>();

		if (eqNode instanceof EqFunctionNode) {

			for (final EqNode arg : ((EqFunctionNode) eqNode).getArgs()) {
				final EqGraphNode argNode = getOrConstructEqGraphNode(arg, eqNodeToEqGraphNode);
				// argNode.addToInitCcpar(graphNode);
				argNode.addToCcpar(graphNode);
				argNodes.add(argNode);
			}
			// graphNode.addToInitCcchild(argNodes);
			graphNode.getCcchild().addPair(new VPArrayIdentifier(((EqFunctionNode) eqNode).getFunction()), argNodes);
		}
		eqNodeToEqGraphNode.put(eqNode, graphNode);
		return graphNode;
	}

	public VPStateBuilder<ACTION> setVars(final Set<IProgramVar> vars) {
		mVars = new HashSet<>(vars);
		return this;
	}

	public VPStateBuilder<ACTION> setEqGraphNodes(final Map<EqNode, EqGraphNode> map) {
		assert map != null;
		mEqNodeToEqGraphNodeMap = map;
		return this;
	}

	@Override
	VPState<ACTION> build() {
		assert mEqNodeToEqGraphNodeMap != null;
		// Set<VPDomainSymmetricPair<VPNodeIdentifier>> disEqualitySet = mDisEqualitySet.stream()
		// .map(pair -> new VPDomainSymmetricPair<>(pair.getFirst().getEqNode(), pair.getFirst().getEqNode()))
		// .collect(Collectors.toSet());
		return new VPState<>(mEqNodeToEqGraphNodeMap, mDisEqualitySet, mVars, mDomain, mIsTop);
	}

	// public VPStateBuilder setDisEqualites(Set<VPDomainSymmetricPair<EqNode>> disEqualitySet) {
	// mDisEqualitySet = disEqualitySet;
	// return this;
	// }

	// public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
	// return mEqGraph.getEqNodeToEqGraphNodeMap();
	// }

	// public Set<VPDomainSymmetricPair<EqNode>> getDisEqualitySet() {
	// return mDisEqualitySet;
	// }

	@Override
	public VPStateBuilder<ACTION> setIsTop(final boolean b) {
		mIsTop = b;
		return this;
	}

//	public void addToDisEqSet(final EqNode node1, final EqNode node2) {
////		getDisEqualitySet().add(new VPDomainSymmetricPair<>(node1, node2));
//		mDisEqualitySet.add(
//				new VPDomainSymmetricPair<VPNodeIdentifier>(
//						new VPNodeIdentifier(node1),
//						new VPNodeIdentifier(node2)));
//	}

	// /**
	// * An additional process after a function node is havoc, in order to restore the propagation.
	// * For example, we have two nodes a[i] and a[j], if i = j, by equality propagation,
	// * we also know a[i] = a[j]. When a[i] is being havoc, we lose the information of a[i] = a[j],
	// * which is the result of equality propagation of (i = j). This method is to restore this
	// * information.
	// *
	// * @param functionNode
	// */
	// void restorePropagation(final EqFunctionNode functionNode) {
	//
	// EqNode firstIndex = functionNode.getArgs().get(0);
	// EqGraphNode firstIndexGN = getEqNodeToEqGraphNodeMap().get(firstIndex);
	//
	// final Set<EqFunctionNode> fnNodeSet = mDomain.getArrayIdToEqFnNodeMap().getImage(functionNode.getFunction());
	// for (final EqFunctionNode fnNode : fnNodeSet) {
	// if (find(getEqNodeToEqGraphNodeMap().get(fnNode.getArgs().get(0))).equals(find(firstIndexGN))) {
	// if (mEqGraph.congruent(getEqNodeToEqGraphNodeMap().get(fnNode), getEqNodeToEqGraphNodeMap().get(functionNode))) {
	// merge(getEqNodeToEqGraphNodeMap().get(fnNode), getEqNodeToEqGraphNodeMap().get(functionNode));
	// }
	// }
	// }
	//
	//// for (final EqFunctionNode fnNode1 : fnNodeSet) {
	//// for (final EqFunctionNode fnNode2 : fnNodeSet) {
	//// if (!fnNode1.equals(fnNode2) && mEqGraph.congruent(getEqNodeToEqGraphNodeMap().get(fnNode1),
	// getEqNodeToEqGraphNodeMap().get(fnNode2))) {
	//// merge(getEqNodeToEqGraphNodeMap().get(fnNode1), getEqNodeToEqGraphNodeMap().get(fnNode2));
	//// }
	//// }
	//// }
	// }

	public void addVariable(final IProgramVar pv) {
		mVars.add(pv);
	}

	public void removeVariable(final IProgramVar pv) {
		mVars.remove(pv);
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}

	public void addVariables(final Collection<IProgramVar> variables) {
		mVars.addAll(variables);
	}

	public void removeVariables(final Collection<IProgramVar> variables) {
		mVars.removeAll(variables);
	}

	public HashRelation<VPArrayIdentifier, List<EqGraphNode>> ccchild(final EqGraphNode representative1) {
		return representative1.find().getCcchild();
	}

	@Override
	EqGraphNode getEqGraphNode(final VPNodeIdentifier id) {
		assert id.getEqNode() != null;
		final EqGraphNode result = mEqNodeToEqGraphNodeMap.get(id.getEqNode());
		assert result != null;
		return result;
	}
}
