package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.HashSet;
import java.util.Set;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqGraphNode {

	public final EqNode eqNode;
	public EqNode find;
	public Set<EqNode> ccpar;
	public Set<EqNode> ccchild;
	public EqNode arg;

	private Set<EqNode> initCcpar;
	private EqNode initCcchild = null;
	
	public EqGraphNode(EqNode eqNode) {
		this.eqNode = eqNode;
		this.find = eqNode;
		this.ccpar = new HashSet<EqNode>();
		this.ccchild = new HashSet<EqNode>();
		this.initCcpar = new HashSet<EqNode>();
	}
	
	public EqGraphNode(EqNode eqNode, EqNode arg) {
		this(eqNode);
		this.arg = arg;
	}
	
	public void setNodeToInitial() {
		this.find = eqNode;
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
		newGraphNode.setFind(this.find);
		newGraphNode.setCcpar(new HashSet<EqNode>(this.ccpar));
		newGraphNode.setCcchild(new HashSet<EqNode>(this.ccchild));
		newGraphNode.addToInitCcpar(this.initCcpar);
		newGraphNode.setInitCcchild(this.initCcchild);
		return newGraphNode;
	}
	
	public EqNode getEqNode() {
		return eqNode;
	}

	public EqNode getFind() {
		return find;
	}

	public void setFind(EqNode find) {
		this.find = find;
	}

	public Set<EqNode> getCcpar() {
		return ccpar;
	}

	public void setCcpar(Set<EqNode> ccpar) {
		this.ccpar = ccpar;
	}
	
	public Set<EqNode> getCcchild() {
		return ccchild;
	}

	public void setCcchild(Set<EqNode> ccchild) {
		this.ccchild = ccchild;
	}
	
	public EqNode getArg() {
		return arg;
	}

	public void setArg(EqNode arg) {
		this.arg = arg;
	}
	
	public void addToInitCcpar(Set<EqNode> initCcpar) {
		this.initCcpar.addAll(initCcpar);
	}
	
	public void addToInitCcpar(EqNode initCcpar) {
		this.initCcpar.add(initCcpar);
	}
	
	public void setInitCcchild(EqNode initCcchild) {
		this.initCcchild = initCcchild;
	}

	public String toString() {
		
		final StringBuilder sb = new StringBuilder();
		
		sb.append(eqNode.toString());
		sb.append(", find: ");
		sb.append(find.toString());
		sb.append(", ccpar: ");
		for (EqNode node : ccpar) {
			sb.append(node.toString());
			sb.append("  ");
		}
		
		return sb.toString();
	}
	
}
