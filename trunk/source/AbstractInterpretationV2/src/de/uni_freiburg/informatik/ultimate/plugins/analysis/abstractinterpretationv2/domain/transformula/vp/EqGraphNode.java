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
public class EqGraphNode {

	public final EqNode eqNode;
	private EqGraphNode representative;
	private Set<EqGraphNode> reverseRepresentative;
	private Set<EqGraphNode> ccpar;
	private HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild;

	private Set<EqGraphNode> initCcpar;
	private List<EqGraphNode> initCcchild;

	public EqGraphNode(EqNode eqNode) {
		this.eqNode = eqNode;
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
	public void setupNode(Map<EqNode, EqGraphNode> eqNodeToEqGraphNode) {
		initCcpar = new HashSet<>();
		for (EqNode par : this.eqNode.getParents()) {
			EqGraphNode gnPar = eqNodeToEqGraphNode.get(par);
			assert gnPar != null;
			initCcpar.add(gnPar);
		}
		initCcpar = Collections.unmodifiableSet(initCcpar);
		
		if (eqNode instanceof EqFunctionNode) {
			EqFunctionNode eqfn = (EqFunctionNode) eqNode;
			initCcchild = eqfn.getArgs().stream().map(eqn -> eqNodeToEqGraphNode.get(eqn)).collect(Collectors.toList());
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
		if (eqNode instanceof EqFunctionNode) {
			this.ccchild.addPair(((EqFunctionNode)eqNode).getFunction(), initCcchild);
		}
	}	
	
	public EqGraphNode find() {
		if (this.getRepresentative().equals(this)) {
			return this;
		}
		return this.getRepresentative().find();
	}

	void copyFields(EqGraphNode other, Map<EqNode, EqGraphNode> eqNodeToEqGraphNode) {
		assert this.eqNode == other.eqNode;
		
		this.setRepresentative(eqNodeToEqGraphNode.get(other.getRepresentative().eqNode));
		
		this.getReverseRepresentative().clear();
		for (EqGraphNode reverseRe : other.getReverseRepresentative()) {
			this.getReverseRepresentative().add(eqNodeToEqGraphNode.get(reverseRe.eqNode));
		}
		this.getCcpar().clear();
		for (EqGraphNode ccpar : other.getCcpar()) {
			this.getCcpar().add(eqNodeToEqGraphNode.get(ccpar.eqNode));
		}
		
		this.ccchild = new HashRelation<>();
		for (IProgramVarOrConst arrayId : other.getCcchild().getDomain()) {
			for (List<EqGraphNode> nodes : other.getCcchild().getImage(arrayId)) {
				List<EqGraphNode> newList = nodes.stream()
						.map(otherNode -> eqNodeToEqGraphNode.get(otherNode.eqNode))
						.collect(Collectors.toList());
				this.getCcchild().addPair(arrayId, newList);
			}
		}
	}

	public EqGraphNode getRepresentative() {
		return representative;
	}

	public void setRepresentative(EqGraphNode representative) {
		this.representative = representative;
		//TODO check
        // if (eqNodes are identical) then (graphnodes must be identical)
        assert this.representative.eqNode != this.eqNode || this.representative == this;
	}

	public Set<EqGraphNode> getReverseRepresentative() {
		return reverseRepresentative;
	}

	public void setReverseRepresentative(Set<EqGraphNode> reverseRepresentative) {
		this.reverseRepresentative = reverseRepresentative;
	}

	public void addToReverseRepresentative(EqGraphNode reverseRepresentative) {
		this.reverseRepresentative.add(reverseRepresentative);
	}

	public Set<EqGraphNode> getCcpar() {
		return ccpar;
	}

	public void setCcpar(Set<EqGraphNode> ccpar) {
		this.ccpar = ccpar;
	}

	public void addToCcpar(EqGraphNode ccpar) {
		this.ccpar.add(ccpar);
	}
	
	public void addToCcpar(Set<EqGraphNode> ccpar) {
		this.ccpar.addAll(ccpar);
	}

	public HashRelation<IProgramVarOrConst, List<EqGraphNode>> getCcchild() {
		return ccchild;
	}
	
	public void addToCcchild(IProgramVarOrConst pVorC, List<EqGraphNode> ccchild) {
		this.ccchild.addPair(pVorC, ccchild);
	}
	
	public Set<EqGraphNode> getInitCcpar() {
		return initCcpar;
	}

//	public void setInitCcpar(Set<EqGraphNode> initCcpar) {
//		this.initCcpar = initCcpar;
//	}
//
//	public void addToInitCcpar(Set<EqGraphNode> initCcpar) {
//		this.initCcpar.addAll(initCcpar);
//	}
//
//	public void addToInitCcpar(EqGraphNode initCcpar) {
//		this.initCcpar.add(initCcpar);
//	}

	public List<EqGraphNode> getInitCcchild() {
		return initCcchild;
	}

	public void setInitCcchild(List<EqGraphNode> initCcchild) {
		this.initCcchild = initCcchild;
	}
//	
//	public void addToInitCcchild(EqGraphNode initCcchild) {
//		this.initCcchild.add(initCcchild);
//	}
//	
//	public void addToInitCcchild(List<EqGraphNode> initCcchild) {
//		this.initCcchild.addAll(initCcchild);
//	}

	public String toString() {

		final StringBuilder sb = new StringBuilder();

		sb.append(eqNode.toString());
		sb.append(" ||| representative: ");
		sb.append(representative.eqNode.toString());
		
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
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof EqGraphNode)) {
			return false;
		}
		return ((EqGraphNode)other).eqNode.equals(this.eqNode);
	}

//	public void setCcchild(Map<Object, Object> newMap) {
//		ccchild = newMap;
//	}
}
