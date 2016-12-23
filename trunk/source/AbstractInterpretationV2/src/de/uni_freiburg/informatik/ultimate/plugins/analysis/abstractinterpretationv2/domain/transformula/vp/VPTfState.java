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
		mTermToNodeId = Collections.unmodifiableMap(termToNodeId);
		mNodeIdToEqGraphNode = Collections.unmodifiableMap(nodeIdToEqGraphNode);
		mArrayIdToFunctionNodes = arrayIdToFunctionNodes.copy();
		
		assert isTopConsistent();
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
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("VPTfState\n");
		sb.append("vars: " + mVars.toString() +"\n");
		sb.append("eqGraphNodes: " + getAllEqGraphNodes().toString() +"\n");
		sb.append("Graph:\n");
		for (EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> egn : getAllEqGraphNodes()) {
			if (egn.getRepresentative() != egn) {
				sb.append(egn.toString() + "\n");
			}
		}
		sb.append("DisEqualities:" + getDisEqualities() + "\n");
		return sb.toString();
	}
}
