package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
	private Set<List<EqGraphNode>> ccchild;

	private Set<EqGraphNode> initCcpar;
	private List<EqGraphNode> initCcchild;

	public EqGraphNode(EqNode eqNode) {
		this.eqNode = eqNode;
		this.representative = this;
		this.reverseRepresentative = new HashSet<>();
		this.ccpar = new HashSet<>();
		this.ccchild = new HashSet<>();
		this.initCcpar = new HashSet<>();
		this.initCcchild = new ArrayList<>();
	}

	public void setNodeToInitial() {
		this.representative = this;
		this.reverseRepresentative.clear();
		this.ccpar.clear();
		this.ccchild.clear();
		if (initCcpar != null) {
			this.ccpar.addAll(initCcpar);
		}
		if (initCcchild != null) {
			this.ccchild.add(initCcchild);
		}
	}

	public EqGraphNode copy() {

		EqGraphNode newGraphNode = new EqGraphNode(this.eqNode);
		newGraphNode.setRepresentative(this);
		newGraphNode.setReverseRepresentative(new HashSet<>(this.reverseRepresentative));
		newGraphNode.setCcpar(new HashSet<>(this.ccpar));
		newGraphNode.setCcchild(new HashSet<>(this.ccchild));
		newGraphNode.addToInitCcpar(this.initCcpar);
		newGraphNode.setInitCcchild(this.initCcchild);
		return newGraphNode;
	}

	public EqGraphNode getRepresentative() {
		return representative;
	}

	public void setRepresentative(EqGraphNode find) {
		this.representative = find;
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

	public Set<List<EqGraphNode>> getCcchild() {
		return ccchild;
	}

	public void setCcchild(Set<List<EqGraphNode>> ccchild) {
		this.ccchild = ccchild;
	}

	public void addToCcchild(List<EqGraphNode> ccchild) {
		this.ccchild.add(ccchild);
	}
	
	public void addToCcchild(Set<List<EqGraphNode>> ccchild) {
		this.ccchild.addAll(ccchild);
	}

	public Set<EqGraphNode> getInitCcpar() {
		return initCcpar;
	}

	public void setInitCcpar(Set<EqGraphNode> initCcpar) {
		this.initCcpar = initCcpar;
	}

	public void addToInitCcpar(Set<EqGraphNode> initCcpar) {
		this.initCcpar.addAll(initCcpar);
	}

	public void addToInitCcpar(EqGraphNode initCcpar) {
		this.initCcpar.add(initCcpar);
	}

	public List<EqGraphNode> getInitCcchild() {
		return initCcchild;
	}

	public void setInitCcchild(List<EqGraphNode> initCcchild) {
		this.initCcchild = initCcchild;
	}
	
	public void addToInitCcchild(EqGraphNode initCcchild) {
		this.initCcchild.add(initCcchild);
	}
	
	public void addToInitCcchild(List<EqGraphNode> initCcchild) {
		this.initCcchild.addAll(initCcchild);
	}

	public String toString() {

		final StringBuilder sb = new StringBuilder();

		sb.append(eqNode.toString());
		sb.append(" ||| representative: ");
		sb.append(representative.eqNode.toString());
		
		sb.append(" ||| reverseRepresentative: ");
		for (EqGraphNode node : reverseRepresentative) {
			sb.append(node.eqNode.toString());
			sb.append("  ");
		}
		sb.append(" ||| ccpar: ");
		for (EqGraphNode node : ccpar) {
			sb.append(node.eqNode.toString());
			sb.append("  ");
		}
		sb.append(" ||| ccchild: ");
		for (List<EqGraphNode> nodes : ccchild) {
			sb.append("{");
			for (EqGraphNode node : nodes) {
				sb.append(node.toString());
				sb.append("  ");
			}
			sb.append("}, ");
		}

		return sb.toString();
	}
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof EqGraphNode)) {
			return false;
		}
		return ((EqGraphNode)other).eqNode.equals(this.eqNode);
	}
}
