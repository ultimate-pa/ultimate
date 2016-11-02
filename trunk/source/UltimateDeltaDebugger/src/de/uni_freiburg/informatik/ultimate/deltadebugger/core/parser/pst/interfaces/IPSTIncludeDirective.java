package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;

public interface IPSTIncludeDirective extends IPSTDirective {
	@Override
	IASTPreprocessorIncludeStatement getASTNode();
}
