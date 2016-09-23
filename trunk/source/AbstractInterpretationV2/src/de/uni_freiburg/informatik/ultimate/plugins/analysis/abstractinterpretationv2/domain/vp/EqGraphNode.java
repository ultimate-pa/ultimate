package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.HashSet;
import java.util.Set;

public class EqGraphNode {

	public final EqNode eqNode;
	public EqNode find;
	public Set<EqNode> ccpar;
	
	public EqNode arg;
	
	public EqGraphNode(EqNode eqNode) {
		this.eqNode = eqNode;
		this.find = eqNode;
		this.ccpar = new HashSet<EqNode>();
	}
	
	public EqGraphNode(EqNode eqNode, EqNode arg) {
		this(eqNode);
		this.arg = arg;
	}
	
	public void setNodeToInitial() {
		this.find = eqNode;
		this.ccpar.clear();
		this.arg = null;
	}
	
	public EqGraphNode copy() {
		
		return new EqGraphNode(eqNode, arg);
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
	
	public EqNode getArg() {
		return arg;
	}

	public void setArg(EqNode arg) {
		this.arg = arg;
	}

	public String toString() {
		return eqNode.toString() + ", find: " + find.toString();
	}
	
}
