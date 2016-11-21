package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

public interface IPSTACSLNode extends IPSTNode {

	ACSLNode getACSLNode();
	
	@Override
	default IASTNode getASTNode() {
		return null;
	}
}
