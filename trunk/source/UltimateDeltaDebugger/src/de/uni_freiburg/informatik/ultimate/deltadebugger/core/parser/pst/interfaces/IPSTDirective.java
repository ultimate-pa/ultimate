package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;

/**
 * A preprocessor directive, e.g. #include, #define, #pragma, #if etc.
 * getASTNode() always returns a non-null IASTPreprocessorStatement (which is
 * admittedly not exactly useful by itself).
 *
 */
public interface IPSTDirective extends IPSTPreprocessorNode {
	@Override
	IASTPreprocessorStatement getASTNode();

	default boolean isConditionalDirective() {
		final IASTPreprocessorStatement statement = getASTNode();
		return statement instanceof IASTPreprocessorIfStatement || statement instanceof IASTPreprocessorIfdefStatement
				|| statement instanceof IASTPreprocessorIfndefStatement
				|| statement instanceof IASTPreprocessorElseStatement
				|| statement instanceof IASTPreprocessorElifStatement
				|| statement instanceof IASTPreprocessorEndifStatement;
	}
}