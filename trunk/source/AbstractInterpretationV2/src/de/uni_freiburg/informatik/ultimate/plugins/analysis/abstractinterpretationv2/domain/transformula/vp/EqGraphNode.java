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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * This class contain information such as representative, reverse
 * representative, ccpar and ccchild of @EqNode. Each @EqNode will map to
 * one @EqGraphNode, i.e., the relation between @EqNode and @EqGraphNode is one
 * to one mapping. Since @EqNode supposed to be immutable, all the mutable
 * information will be handled by this class.
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqGraphNode<NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> {

	/**
	 * identifies an EqGraphNode uniquely _within one state or transitionstate_
	 */
	public final NODEID nodeIdentifier;
	private EqGraphNode<NODEID, ARRAYID> representative;
	private Set<EqGraphNode<NODEID, ARRAYID>> reverseRepresentative;
	private Set<EqGraphNode<NODEID, ARRAYID>> ccpar;
	private HashRelation<ARRAYID, List<EqGraphNode<NODEID, ARRAYID>>> ccchild;

	private Set<EqGraphNode<NODEID, ARRAYID>> initCcpar;
	private List<EqGraphNode<NODEID, ARRAYID>> initCcchild;

	public EqGraphNode(NODEID id) {
		assert id != null;
//		this.nodeIdentifier = new VPNodeIdentifier(eqNode);
		this.nodeIdentifier = id;
		this.representative = this;
		this.reverseRepresentative = new HashSet<>();
		this.ccpar = new HashSet<>();
		this.ccchild = new HashRelation<>();
		this.initCcpar = null;
		this.initCcchild = null;
	}
	
	/**
	 * This may only be called when all EqGraphNodes for the given state (and thus mapping form Eqnodes to EqGraphNodes)
	 * have been created.
	 * Then this method sets up initCCpar and initCcchild according to the mapping and the parent/argument information in
	 * the EqNode
	 * @param eqNodeToEqGraphNode
	 */
	public void setupNode() {
		initCcpar = new HashSet<>(this.ccpar);
		initCcpar = Collections.unmodifiableSet(initCcpar);
		
		if (nodeIdentifier.isFunction()) {
			ARRAYID arrayId = nodeIdentifier.getFunction();
			assert this.ccchild.getImage(arrayId).size() == 1;
			initCcchild = new ArrayList<>(this.ccchild.getImage(arrayId).iterator().next());
			initCcchild = Collections.unmodifiableList(initCcchild);
		}
	}

	public void setNodeToInitial() {
		this.representative = this;
		this.reverseRepresentative.clear();
		this.ccpar.clear();
		this.ccpar.addAll(initCcpar);

		this.ccchild = new HashRelation<>();
		/*
		 * Only function node have initCcchild.
		 */
		if (nodeIdentifier.isFunction()) {
			this.ccchild.addPair(nodeIdentifier.getFunction(), initCcchild);
		}
	}	
	
	public EqGraphNode<NODEID, ARRAYID> find() {
		if (this.getRepresentative().equals(this)) {
			return this;
		}
		return this.getRepresentative().find();
	}

	static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> void copyFields(
			EqGraphNode<NODEID, ARRAYID> source, EqGraphNode<NODEID, ARRAYID> target, IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder) {
		assert target.nodeIdentifier.equals(source.nodeIdentifier);
		
		target.setRepresentative(builder.getEqGraphNode(source.getRepresentative().nodeIdentifier));
		
		target.getReverseRepresentative().clear();
		for (EqGraphNode<NODEID, ARRAYID> reverseRe : source.getReverseRepresentative()) {
			target.getReverseRepresentative().add(builder.getEqGraphNode(reverseRe.nodeIdentifier));
		}
		target.getCcpar().clear();
		for (EqGraphNode<NODEID, ARRAYID> ccpar : source.getCcpar()) {
			target.getCcpar().add(builder.getEqGraphNode(ccpar.nodeIdentifier));
		}
		
		target.ccchild = new HashRelation<>();
		for (ARRAYID arrayId : source.getCcchild().getDomain()) {
			for (List<EqGraphNode<NODEID, ARRAYID>> nodes : source.getCcchild().getImage(arrayId)) {
				List<EqGraphNode<NODEID, ARRAYID>> newList = nodes.stream()
						.map(otherNode -> builder.getEqGraphNode(otherNode.nodeIdentifier))
						.collect(Collectors.toList());
				target.getCcchild().addPair(arrayId, newList);
			}
		}
	}

	public EqGraphNode<NODEID, ARRAYID> getRepresentative() {
		return representative;
	}

	public void setRepresentative(EqGraphNode<NODEID, ARRAYID> representative) {
		this.representative = representative;
		//TODO check
        // if (eqNodes are identical) then (graphnodes must be identical)
        assert this.representative.nodeIdentifier != this.nodeIdentifier || this.representative == this;
	}

	public Set<EqGraphNode<NODEID, ARRAYID>> getReverseRepresentative() {
		return reverseRepresentative;
	}

	public void setReverseRepresentative(Set<EqGraphNode<NODEID, ARRAYID>> reverseRepresentative) {
		this.reverseRepresentative = reverseRepresentative;
	}

	public void addToReverseRepresentative(EqGraphNode<NODEID, ARRAYID> reverseRepresentative) {
		this.reverseRepresentative.add(reverseRepresentative);
	}

	public Set<EqGraphNode<NODEID, ARRAYID>> getCcpar() {
		return ccpar;
	}

	public void setCcpar(Set<EqGraphNode<NODEID, ARRAYID>> ccpar) {
		this.ccpar = ccpar;
	}

	public void addToCcpar(EqGraphNode<NODEID, ARRAYID> ccpar) {
		this.ccpar.add(ccpar);
	}
	
	public void addToCcpar(Set<EqGraphNode<NODEID, ARRAYID>> ccpar) {
		this.ccpar.addAll(ccpar);
	}

	public HashRelation<ARRAYID, List<EqGraphNode<NODEID, ARRAYID>>> getCcchild() {
		return ccchild;
	}
	
	public void addToCcchild(ARRAYID pVorC, List<EqGraphNode<NODEID, ARRAYID>> ccchild) {
		this.ccchild.addPair(pVorC, ccchild);
	}
	
	public Set<EqGraphNode<NODEID, ARRAYID>> getInitCcpar() {
		return initCcpar;
	}

	public List<EqGraphNode<NODEID, ARRAYID>> getInitCcchild() {
		return initCcchild;
	}

	public void setInitCcchild(List<EqGraphNode<NODEID, ARRAYID>> initCcchild) {
		this.initCcchild = initCcchild;
	}

	public String toString() {

		final StringBuilder sb = new StringBuilder();

		sb.append(nodeIdentifier.toString());
		sb.append(" ||| representative: ");
		sb.append(representative.nodeIdentifier.toString());
		
//		sb.append(" ||| reverseRepresentative: ");
//		for (EqGraphNode node : reverseRepresentative) {
//			sb.append(node.eqNode.toString());
//			sb.append("  ");
//		}
//		sb.append(" ||| ccpar: ");
//		for (EqGraphNode node : ccpar) {
//			sb.append(node.eqNode.toString());
//			sb.append("  ");
//		}
//		sb.append(" ||| ccchild: ");
//		for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : ccchild.entrySet()) {
//			sb.append(entry.getKey().toString() + ": {");
//			for (EqGraphNode node : entry.getValue()) {
//				sb.append(node.toString());
//				sb.append("  ");
//			}
//			sb.append("}, ");
//		}

		return sb.toString();
	}
	
//	@Override
//	public boolean equals(Object other) {
//		if (!(other instanceof EqGraphNode)) {
//			return false;
//		}
//		//TODO: what is this for??
//		assert false;
//		return ((EqGraphNode)other).nodeIdentifier.equals(this.nodeIdentifier);
//	}

//	public void setCcchild(Map<Object, Object> newMap) {
//		ccchild = newMap;
//	}

}
