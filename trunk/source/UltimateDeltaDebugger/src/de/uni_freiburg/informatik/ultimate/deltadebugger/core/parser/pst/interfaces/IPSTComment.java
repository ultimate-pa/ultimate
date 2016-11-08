package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTComment;

public interface IPSTComment extends IPSTPreprocessorNode {
	@Override
	IASTComment getASTNode();
}
