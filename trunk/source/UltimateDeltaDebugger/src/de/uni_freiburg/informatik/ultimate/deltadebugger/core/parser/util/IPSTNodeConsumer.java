package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTPreprocessorNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;

/**
 * Simluate a double dispatch function for an IPSTNode argument. Analoguous to
 * IASTNodeConsumer for consistency reasons.
 *
 */
public interface IPSTNodeConsumer {

	void on(IPSTNode node);

	default void on(IPSTConditionalBlock conditionalBlock) {
		on((IPSTNode) conditionalBlock);
	}

	default void on(IPSTLiteralRegion literalRegion) {
		on((IPSTNode) literalRegion);
	}

	default void on(IPSTPreprocessorNode preprocessOrNode) {
		on((IPSTNode) preprocessOrNode);
	}

	default void on(IPSTComment comment) {
		on((IPSTPreprocessorNode) comment);
	}

	default void on(IPSTDirective directive) {
		on((IPSTPreprocessorNode) directive);
	}

	default void on(IPSTIncludeDirective includeDirective) {
		on((IPSTDirective) includeDirective);
	}

	default void on(IPSTMacroExpansion macroExpansion) {
		on((IPSTPreprocessorNode) macroExpansion);
	}

	default void on(IPSTRegularNode node) {
		on((IPSTNode) node);
	}

	default void on(IPSTTranslationUnit translationUnit) {
		on((IPSTRegularNode) translationUnit);
	}
}
