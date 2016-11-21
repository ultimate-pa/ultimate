package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
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
 * Simulate a double dispatch function for an IPSTNode argument. Analogous to IASTNodeConsumer for consistency reasons.
 *
 */
@FunctionalInterface
public interface IPSTNodeConsumer {

	default void on(final IPSTComment comment) {
		on((IPSTPreprocessorNode) comment);
	}

	default void on(final IPSTACSLComment acslComment) {
		on((IPSTComment) acslComment);
	}
	
	default void on(final IPSTACSLNode acslNode) {
		on((IPSTNode) acslNode);
	}
	
	default void on(final IPSTConditionalBlock conditionalBlock) {
		on((IPSTNode) conditionalBlock);
	}

	default void on(final IPSTDirective directive) {
		on((IPSTPreprocessorNode) directive);
	}

	default void on(final IPSTIncludeDirective includeDirective) {
		on((IPSTDirective) includeDirective);
	}

	default void on(final IPSTLiteralRegion literalRegion) {
		on((IPSTNode) literalRegion);
	}

	default void on(final IPSTMacroExpansion macroExpansion) {
		on((IPSTPreprocessorNode) macroExpansion);
	}

	void on(IPSTNode node);

	default void on(final IPSTPreprocessorNode preprocessOrNode) {
		on((IPSTNode) preprocessOrNode);
	}

	default void on(final IPSTRegularNode node) {
		on((IPSTNode) node);
	}

	default void on(final IPSTTranslationUnit translationUnit) {
		on((IPSTRegularNode) translationUnit);
	}
}
