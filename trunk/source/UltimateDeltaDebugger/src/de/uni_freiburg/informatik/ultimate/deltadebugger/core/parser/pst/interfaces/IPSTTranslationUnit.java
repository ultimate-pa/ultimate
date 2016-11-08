package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

public interface IPSTTranslationUnit extends IPSTRegularNode {
	@Override
	IASTTranslationUnit getASTNode();
}
