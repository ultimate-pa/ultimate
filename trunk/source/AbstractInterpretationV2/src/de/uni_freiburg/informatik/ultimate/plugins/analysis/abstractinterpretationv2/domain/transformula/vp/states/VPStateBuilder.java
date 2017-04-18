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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class VPStateBuilder<ACTION extends IIcfgTransition<IcfgLocation>>
		extends IVPStateOrTfStateBuilder<VPState<ACTION>, EqNode, IProgramVarOrConst> {

	protected final Set<IProgramVarOrConst> mVars = new HashSet<>();
	
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
		for (final EqNode eqNode : mDomain.getPreAnalysis().getTermToEqNodeMap().values()) {
			getOrConstructEqGraphNode(eqNode, eqNodeToEqGraphNodeMap);
		}
		mEqNodeToEqGraphNodeMap = Collections.unmodifiableMap(eqNodeToEqGraphNodeMap);
	}

	private EqGraphNode<EqNode, IProgramVarOrConst> getOrConstructEqGraphNode(final EqNode eqNode,
			final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> eqNodeToEqGraphNode) {

		if (eqNodeToEqGraphNode.containsKey(eqNode)) {
			return eqNodeToEqGraphNode.get(eqNode);
		}

		final EqGraphNode<EqNode, IProgramVarOrConst> graphNode = new EqGraphNode<>(eqNode);
		final List<EqGraphNode<EqNode, IProgramVarOrConst>> argNodes = new ArrayList<>();

		if (eqNode instanceof EqFunctionNode) {

			for (final EqNode arg : ((EqFunctionNode) eqNode).getArgs()) {
				final EqGraphNode<EqNode, IProgramVarOrConst> argNode = getOrConstructEqGraphNode(arg, eqNodeToEqGraphNode);
				argNode.addToCcpar(graphNode);
				argNodes.add(argNode);
			}
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
	public VPState<ACTION> build() {
		assert mEqNodeToEqGraphNodeMap != null;
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);
		return new VPState<>(mEqNodeToEqGraphNodeMap, mDisEqualitySet, mVars, mDomain, mIsTop);
	}

	@Override
	public VPStateBuilder<ACTION> setIsTop(final boolean b) {
		mIsTop = b;
		return this;
	}

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

		 final Set<EqFunctionNode> fnNodeSet = mDomain.getPreAnalysis().getArrayIdToFnNodeMap().getImage(functionNode.getFunction());
		 for (final EqFunctionNode fnNode : fnNodeSet) {
			 if (getEqGraphNode(fnNode.getArgs().get(0)).find().equals(firstIndexGN.find())) {
				 if (congruent(getEqGraphNode(fnNode), getEqGraphNode(functionNode))) {
					 merge(getEqGraphNode(fnNode), getEqGraphNode(functionNode));
				 }
			 }
		 }
	 }

	public HashRelation<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> ccchild(final EqGraphNode<EqNode, IProgramVarOrConst> representative1) {
		return representative1.find().getCcchild();
	}

	@Override
	public EqGraphNode<EqNode, IProgramVarOrConst> getEqGraphNode(final EqNode id) {
		assert id != null;
		final EqGraphNode<EqNode, IProgramVarOrConst> result = mEqNodeToEqGraphNodeMap.get(id);
		assert result != null;
		return result;
	}

	@Override
	Collection<EqGraphNode<EqNode, IProgramVarOrConst>> getAllEqGraphNodes() {
		return mEqNodeToEqGraphNodeMap.values();
	}
	
	public void clearDisEqualitySet() {
		mDisEqualitySet.clear();
	}

	public Set<VPDomainSymmetricPair<EqNode>> getDisEqualitySet() {
		return Collections.unmodifiableSet(mDisEqualitySet);
	}

	public VPStateBuilder<ACTION> addVars(final Collection<IProgramVarOrConst> variables) {
		mVars.addAll(variables);
		return this;
	}

	public VPStateBuilder<ACTION> removeVars(final Collection<IProgramVarOrConst> variables) {
		mVars.removeAll(variables);
		return this;
	}
}
