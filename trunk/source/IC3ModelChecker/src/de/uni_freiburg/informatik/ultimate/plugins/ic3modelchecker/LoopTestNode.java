package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.ArrayList;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class LoopTestNode {
	private CFGExplicitNode node;
	private ArrayList<CFGExplicitNode> ancestors;
	
	public LoopTestNode(CFGExplicitNode node, ArrayList<CFGExplicitNode> ancestors) {
		this.node = node;
		this.ancestors = ancestors;
	}
	
	public CFGExplicitNode getNode() {
		return node;
	}
	
	public ArrayList<CFGExplicitNode> getAncestors() {
		return ancestors;
	}
}
