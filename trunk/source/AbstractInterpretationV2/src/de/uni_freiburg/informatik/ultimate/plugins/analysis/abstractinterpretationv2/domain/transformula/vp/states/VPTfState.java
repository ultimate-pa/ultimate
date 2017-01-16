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

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPTfState extends IVPStateOrTfState<VPTfNodeIdentifier, VPTfArrayIdentifier> {
	
//	private final Map<Term, VPTfNodeIdentifier> mTermToNodeId;
	private final VPTfStateBuilder mBuilder;
	private final TransFormula mTransFormula;
	private final HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> mArrayIdToFunctionNodes;
	private final Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mNodeIdToEqGraphNode;
	private final Set<VPTfNodeIdentifier> mAllNodeIds;


	public VPTfState(TransFormula tf,
			VPTfStateBuilder builder,
			Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> nodeIdToEqGraphNode,
//			Map<Term, VPTfNodeIdentifier> termToNodeId,
			Set<VPTfNodeIdentifier> allNodeIds,
			HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> arrayIdToFunctionNodes,
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqs, 
			boolean isTop, 
			Set<IProgramVar> vars) {
		super(disEqs, isTop, vars);
		mTransFormula = tf;
		mBuilder = builder;
//		mTermToNodeId = Collections.unmodifiableMap(termToNodeId);
		mAllNodeIds = allNodeIds;
		mNodeIdToEqGraphNode = Collections.unmodifiableMap(nodeIdToEqGraphNode);
		mArrayIdToFunctionNodes = arrayIdToFunctionNodes.copy(); // TODO is copy needed here?
		
		assert isTopConsistent();
	}

//	public boolean tracksTerm(Term term) {
//		return mTermToNodeId.containsKey(term);
//	}

	public boolean isBottom() {
		return false;
	}

	@Override
	public EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getEqGraphNode(VPTfNodeIdentifier nodeIdentifier) {
		return mNodeIdToEqGraphNode.get(nodeIdentifier);
	}

	@Override
	public Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> getAllEqGraphNodes() {
		return new HashSet<>(mNodeIdToEqGraphNode.values());
	}

	@Override
	public VPTfNodeIdentifier find(VPTfNodeIdentifier id) {
		return mNodeIdToEqGraphNode.get(id).find().nodeIdentifier;
	}

	public Set<VPTfNodeIdentifier> getFunctionNodesForArray(VPTfArrayIdentifier array) {
		return mArrayIdToFunctionNodes.getImage(array);
	}

	public TransFormula getTransFormula() {
		return mTransFormula;
	}
	
//	public VPTfNodeIdentifier getNodeId(Term t) {
//		return mTermToNodeId.get(t);
//	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("VPTfState\n");
		sb.append("vars: " + mVars.toString() +"\n");
		//sb.append("eqGraphNodes: " + getAllEqGraphNodes().toString() +"\n");
		sb.append("Graph:\n");
		for (EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egn : getAllEqGraphNodes()) {
			if (egn.getRepresentative() != egn) {
				sb.append(egn.toString() + "\n");
			}
		}
		sb.append("DisEqualities:" + getDisEqualities() + "\n");
		return sb.toString();
	}

	public VPTfArrayIdentifier getArrayIdentifier(Term newArray) {
		assert mBuilder.getTransFormula() == mTransFormula;
		return mBuilder.getOrConstructArrayIdentifier(newArray);
	}
}
