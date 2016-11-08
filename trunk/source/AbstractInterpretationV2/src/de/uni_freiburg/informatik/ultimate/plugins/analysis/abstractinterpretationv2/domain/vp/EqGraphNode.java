package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.HashSet;
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
	private EqNode arg;
	private EqNode representative;
	private Set<EqNode> reverseRepresentative;
	private Set<EqNode> ccpar;
	private Set<EqNode> ccchild;

	private Set<EqNode> initCcpar;
	private EqNode initCcchild = null;

	public EqGraphNode(EqNode eqNode) {
		this.eqNode = eqNode;
		this.representative = eqNode;
		this.reverseRepresentative = new HashSet<EqNode>();
		this.ccpar = new HashSet<EqNode>();
		this.ccchild = new HashSet<EqNode>();
		this.initCcpar = new HashSet<EqNode>();
	}

	public EqGraphNode(EqNode eqNode, EqNode arg) {
		this(eqNode);
		this.arg = arg;
	}

	public void setNodeToInitial() {
		this.representative = eqNode;
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

		EqGraphNode newGraphNode = new EqGraphNode(this.eqNode, this.arg);
		newGraphNode.setRepresentative(this.representative);
		newGraphNode.setReverseRepresentative(new HashSet<EqNode>(this.reverseRepresentative));
		newGraphNode.setCcpar(new HashSet<EqNode>(this.ccpar));
		newGraphNode.setCcchild(new HashSet<EqNode>(this.ccchild));
		newGraphNode.addToInitCcpar(this.initCcpar);
		newGraphNode.setInitCcchild(this.initCcchild);
		return newGraphNode;
	}

	public EqNode getArg() {
		return arg;
	}

	public void setArg(EqNode arg) {
		this.arg = arg;
	}

	public EqNode getRepresentative() {
		return representative;
	}

	public void setRepresentative(EqNode find) {
		this.representative = find;
	}

	public Set<EqNode> getReverseRepresentative() {
		return reverseRepresentative;
	}

	public void setReverseRepresentative(Set<EqNode> reverseRepresentative) {
		this.reverseRepresentative = reverseRepresentative;
	}

	public void addToReverseRepresentative(EqNode reverseRepresentative) {
		this.reverseRepresentative.add(reverseRepresentative);
	}

	public Set<EqNode> getCcpar() {
		return ccpar;
	}

	public void setCcpar(Set<EqNode> ccpar) {
		this.ccpar = ccpar;
	}

	public void addToCcpar(EqNode ccpar) {
		this.ccpar.add(ccpar);
	}
	
	public void addToCcpar(Set<EqNode> ccpar) {
		this.ccpar.addAll(ccpar);
	}

	public Set<EqNode> getCcchild() {
		return ccchild;
	}

	public void setCcchild(Set<EqNode> ccchild) {
		this.ccchild = ccchild;
	}

	public void addToCcchild(EqNode ccchild) {
		this.ccchild.add(ccchild);
	}
	
	public void addToCcchild(Set<EqNode> ccchild) {
		this.ccchild.addAll(ccchild);
	}

	public Set<EqNode> getInitCcpar() {
		return initCcpar;
	}

	public void setInitCcpar(Set<EqNode> initCcpar) {
		this.initCcpar = initCcpar;
	}

	public void addToInitCcpar(Set<EqNode> initCcpar) {
		this.initCcpar.addAll(initCcpar);
	}

	public void addToInitCcpar(EqNode initCcpar) {
		this.initCcpar.add(initCcpar);
	}

	public EqNode getInitCcchild() {
		return initCcchild;
	}

	public void setInitCcchild(EqNode initCcchild) {
		this.initCcchild = initCcchild;
	}

	public String toString() {

		final StringBuilder sb = new StringBuilder();

		sb.append(eqNode.toString());
		sb.append(" ||| representative: ");
		sb.append(representative.toString());
		sb.append(" ||| reverseRepresentative: ");
		for (EqNode node : reverseRepresentative) {
			sb.append(node.toString());
			sb.append("  ");
		}
		sb.append(" ||| ccpar: ");
		for (EqNode node : ccpar) {
			sb.append(node.toString());
			sb.append("  ");
		}
		sb.append(" ||| ccchild: ");
		for (EqNode node : ccchild) {
			sb.append(node.toString());
			sb.append("  ");
		}

		return sb.toString();
	}

}
