package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTNode;

/**
 * A literal region represents an unexpanded source region that should be ignored. There is no corresponding IASTNode in
 * the original AST, so getASTNode() always returns null.
 */
public interface IPSTLiteralRegion extends IPSTNode {
	@Override
	default IASTNode getASTNode() {
		return null;
	}
}