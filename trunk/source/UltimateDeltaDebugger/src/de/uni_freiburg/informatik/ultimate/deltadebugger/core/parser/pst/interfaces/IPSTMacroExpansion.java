package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;

public interface IPSTMacroExpansion extends IPSTPreprocessorNode {
	@Override
	IASTPreprocessorMacroExpansion getASTNode();
}