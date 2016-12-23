/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class VPStateBuilder<ACTION extends IIcfgTransition<IcfgLocation>>
		extends IVPStateOrTfStateBuilder<VPState<ACTION>, EqNode, IProgramVarOrConst> {

	protected final VPDomain<ACTION> mDomain;

	private Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> mEqNodeToEqGraphNodeMap;

	public VPStateBuilder(final VPDomain<ACTION> domain) {
		mDomain = domain;
		createEqGraphNodes();
	}

	protected VPStateBuilder(final VPDomain<ACTION> domain, final boolean dontCreateEqGraphNodes) {
		assert dontCreateEqGraphNodes;
		mDomain = domain;
	}

	private void createEqGraphNodes() {
		/*
		 * Create fresh EqGraphNodes from EqNodes.
		 */
		final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> eqNodeToEqGraphNodeMap = new HashMap<>();
		for (final EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			getOrConstructEqGraphNode(eqNode, eqNodeToEqGraphNodeMap);
		}
		mEqNodeToEqGraphNodeMap = Collections.unmodifiableMap(eqNodeToEqGraphNodeMap);
	}

	private EqGraphNode<EqNode, IProgramVarOrConst> getOrConstructEqGraphNode(final EqNode eqNode,
			final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> eqNodeToEqGraphNode) {

		if (eqNodeToEqGraphNode.containsKey(eqNode)) {
			return eqNodeToEqGraphNode.get(eqNode);
		}

		final EqGraphNode<EqNode, IProgramVarOrConst> graphNode = new EqGraphNode(eqNode);
		final List<EqGraphNode<EqNode, IProgramVarOrConst>> argNodes = new ArrayList<>();

		if (eqNode instanceof EqFunctionNode) {

			for (final EqNode arg : ((EqFunctionNode) eqNode).getArgs()) {
				final EqGraphNode<EqNode, IProgramVarOrConst> argNode = getOrConstructEqGraphNode(arg, eqNodeToEqGraphNode);
				// argNode.addToInitCcpar(graphNode);
				argNode.addToCcpar(graphNode);
				argNodes.add(argNode);
			}
			// graphNode.addToInitCcchild(argNodes);
			graphNode.getCcchild().addPair(eqNode.getFunction(), argNodes);
		}
		eqNodeToEqGraphNode.put(eqNode, graphNode);
		return graphNode;
	}

	public VPStateBuilder<ACTION> setEqGraphNodes(final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> map) {
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

	 /**
	 * An additional process after a function node is havoc, in order to restore the propagation.
	 * For example, we have two nodes a[i] and a[j], if i = j, by equality propagation,
	 * we also know a[i] = a[j]. When a[i] is being havoc, we lose the information of a[i] = a[j],
	 * which is the result of equality propagation of (i = j). This method is to restore this
	 * information.
	 *
	 * @param functionNode
	 */
	 void restorePropagation(final EqFunctionNode functionNode) {
	
		 EqNode firstIndex = functionNode.getArgs().get(0);
		 EqGraphNode<EqNode, IProgramVarOrConst> firstIndexGN = getEqGraphNode(firstIndex);

		 final Set<EqFunctionNode> fnNodeSet = mDomain.getArrayIdToEqFnNodeMap().getImage(functionNode.getFunction());
		 for (final EqFunctionNode fnNode : fnNodeSet) {
			 if (getEqGraphNode(fnNode.getArgs().get(0)).find().equals(firstIndexGN.find())) {
				 if (congruent(getEqGraphNode(fnNode), getEqGraphNode(functionNode))) {
					 merge(getEqGraphNode(fnNode), getEqGraphNode(functionNode));
				 }
			 }
		 }

		 // for (final EqFunctionNode fnNode1 : fnNodeSet) {
		 // for (final EqFunctionNode fnNode2 : fnNodeSet) {
		 // if (!fnNode1.equals(fnNode2) && mEqGraph.congruent(getEqNodeToEqGraphNodeMap().get(fnNode1),
//		 getEqNodeToEqGraphNodeMap().get(fnNode2))) {
			 // merge(getEqNodeToEqGraphNodeMap().get(fnNode1), getEqNodeToEqGraphNodeMap().get(fnNode2));
			 // }
			 // }
			 // }
	 }

//	public void addVariable(final IProgramVar pv) {
//		mVars.add(pv);
//	}

//	public void removeVariable(final IProgramVar pv) {
//		mVars.remove(pv);
//	}

//	public Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> getEqNodeToEqGraphNodeMap() {
//		return mEqNodeToEqGraphNodeMap;
//	}

//	public void addVariables(final Collection<IProgramVar> variables) {
//		mVars.addAll(variables);
//	}
//
//	public void removeVariables(final Collection<IProgramVar> variables) {
//		mVars.removeAll(variables);
//	}

	public HashRelation<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> ccchild(final EqGraphNode<EqNode, IProgramVarOrConst> representative1) {
		return representative1.find().getCcchild();
	}

	@Override
	EqGraphNode<EqNode, IProgramVarOrConst> getEqGraphNode(final EqNode id) {
		assert id != null;
		final EqGraphNode<EqNode, IProgramVarOrConst> result = mEqNodeToEqGraphNodeMap.get(id);
		assert result != null;
		return result;
	}

	@Override
	Collection<EqGraphNode<EqNode, IProgramVarOrConst>> getAllEqGraphNodes() {
		return mEqNodeToEqGraphNodeMap.values();
	}

	public Set<VPDomainSymmetricPair<EqNode>> getDisEqualitySet() {
		return Collections.unmodifiableSet(mDisEqualitySet);
	}
}
