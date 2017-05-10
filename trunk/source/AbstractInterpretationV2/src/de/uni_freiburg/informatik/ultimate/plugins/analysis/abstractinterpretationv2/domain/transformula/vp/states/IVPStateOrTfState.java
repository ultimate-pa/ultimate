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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <NODEID>
 * @param <ARRAYID>
 */
public abstract class IVPStateOrTfState<NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> {
	
	private final Set<VPDomainSymmetricPair<NODEID>> mDisEqualitySet;
	private final boolean mIsTop;
	
	
	private final Map<NODEID, EqGraphNode<NODEID, ARRAYID>> mNodeIdToEqGraphNode;
	
	
	// debug setting
	protected boolean mLogAsGraph = false;

	private final HashRelation<EqGraphNode<NODEID, ARRAYID>, EqGraphNode<NODEID, ARRAYID>> mAllEqGraphNodePairs;

	public IVPStateOrTfState(final Set<VPDomainSymmetricPair<NODEID>> disEqs, final boolean isTop, 
			Map<NODEID, EqGraphNode<NODEID, ARRAYID>> nodeIdToEqGraphNode) {
		mNodeIdToEqGraphNode = nodeIdToEqGraphNode == null ? null : Collections.unmodifiableMap(nodeIdToEqGraphNode);
		mDisEqualitySet = disEqs == null ? null : Collections.unmodifiableSet(disEqs);
		mIsTop = isTop;
		
		// precompute all pairs of EqGraphNodes (for the corresponding getter)
		if (nodeIdToEqGraphNode == null) {
			mAllEqGraphNodePairs = null;
			return;
		}
		final List<EqGraphNode<NODEID, ARRAYID>> nodesList = new ArrayList<>(nodeIdToEqGraphNode.values());
		mAllEqGraphNodePairs = new HashRelation<>();
		for (int i = 0; i < nodesList.size(); i++) {
			for (int j = 0; j < i; j++) {
				mAllEqGraphNodePairs.addPair(nodesList.get(i), nodesList.get(j));
			}
		}
	}

	public Set<NODEID> getDisequalities(final NODEID nodeIdentifer) {
		final Set<NODEID> result = new HashSet<>();
		for (final VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (pair.contains(nodeIdentifer)) {
				result.add(pair.getOther(nodeIdentifer));
			}
		}
		return result;
	}
	
	public Set<VPDomainSymmetricPair<NODEID>> getDisEqualities() {
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);
		return mDisEqualitySet;
	}
	
	public abstract boolean isBottom();
	
	public boolean isTop() {
		return mIsTop;
	}


	/**
	 * just a convenient interface for the disequality set --> difference to areUnEqual: does not do a find(..) on the
	 * given nodes
	 *
	 * @param nodeId1
	 * @param nodeId2
	 * @return
	 */
	public boolean containsDisEquality(final NODEID nodeId1, final NODEID nodeId2) {
		return mDisEqualitySet.contains(new VPDomainSymmetricPair<NODEID>(nodeId1, nodeId2));
	}
	
	/**
	 * Determines if the given nodes are unequal in this state. (difference to containsDisEquality: does a find(..) on
	 * the nodes)
	 *
	 * @param nodeIdentifier1
	 * @param nodeIdentifier2
	 * @return
	 */
	public boolean areUnEqual(final NODEID nodeIdentifier1, final NODEID nodeIdentifier2) {
		final NODEID find1 = find(nodeIdentifier1);
		final NODEID find2 = find(nodeIdentifier2);
		return containsDisEquality(find1, find2);
	}

	public boolean areEqual(final NODEID nodeIdentifier1, final NODEID nodeIdentifier2) {
		final NODEID find1 = find(nodeIdentifier1);
		final NODEID find2 = find(nodeIdentifier2);
		return find1.equals(find2);
	}
	
	final public EqGraphNode<NODEID, ARRAYID> getEqGraphNode(NODEID nodeIdentifier) {
		return mNodeIdToEqGraphNode.get(nodeIdentifier);
	}

	final public Collection<EqGraphNode<NODEID, ARRAYID>> getAllEqGraphNodes() {
		return mNodeIdToEqGraphNode.values();
	}
	
	final public HashRelation<EqGraphNode<NODEID, ARRAYID>, EqGraphNode<NODEID, ARRAYID>> getAllEqGraphNodePairs() {
		return mAllEqGraphNodePairs;
	}

	final public NODEID find(NODEID id) {
		return mNodeIdToEqGraphNode.get(id).find().mNodeIdentifier;
	}

	protected boolean isTopConsistent() {
		if (!mIsTop) {
			return true;
		}
		for (final VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (!pair.getFirst().isLiteral() || !pair.getSecond().isLiteral()) {
				return false;
			}
		}

		for (final EqGraphNode<NODEID, ARRAYID> egn : getAllEqGraphNodes()) {
			if (egn.getRepresentative() != egn) {
				return false;
			}
		}
		return true;
	}
	
	public Set<NODEID> getEquivalenceRepresentatives() {
		final Set<NODEID> result = new HashSet<>();
		for (final EqGraphNode<NODEID, ARRAYID> egn : mNodeIdToEqGraphNode.values()) {
			if (egn.getRepresentative() == egn) {
				result.add(egn.mNodeIdentifier);
			}
		}
		return result;
	}

	/**
	 * TODO: more efficient implementation? (of the methods using this method?)
	 *
	 * @param node
	 * @return All the eqNodes that are in the same equivalence class as node in this state.
	 */
	public Set<NODEID> getEquivalentEqNodes(final NODEID node) {
		if (node == null) {
			return Collections.emptySet();
		}
		final EqGraphNode<NODEID, ARRAYID> nodeGraphNode = mNodeIdToEqGraphNode.get(node);
		final Set<NODEID> result = new HashSet<>();
		for (final EqGraphNode<NODEID, ARRAYID> egn : mNodeIdToEqGraphNode.values()) {
			if (egn.find() == nodeGraphNode.find()) {
				result.add(egn.mNodeIdentifier);
			}
		}
		return result;
	}

	public Map<NODEID, EqGraphNode<NODEID, ARRAYID>> getNodeIdToEqGraphNode() {
		return mNodeIdToEqGraphNode;
	}
}
