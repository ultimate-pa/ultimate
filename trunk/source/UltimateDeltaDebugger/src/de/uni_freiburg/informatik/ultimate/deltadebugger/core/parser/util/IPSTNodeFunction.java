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
 * Simluate a double dispatch function for an IPSTNode argument. Analoguous to IASTNodeFunction for consistency reasons.
 *
 * @param <T>
 *            returned type
 */
@FunctionalInterface
public interface IPSTNodeFunction<T> {

	default T on(final IPSTComment comment) {
		return on((IPSTPreprocessorNode) comment);
	}

	default T on(final IPSTConditionalBlock conditionalBlock) {
		return on((IPSTNode) conditionalBlock);
	}

	default T on(final IPSTDirective directive) {
		return on((IPSTPreprocessorNode) directive);
	}

	default T on(final IPSTIncludeDirective includeDirective) {
		return on((IPSTDirective) includeDirective);
	}

	default T on(final IPSTLiteralRegion literalRegion) {
		return on((IPSTNode) literalRegion);
	}

	default T on(final IPSTMacroExpansion macroExpansion) {
		return on((IPSTPreprocessorNode) macroExpansion);
	}

	T on(IPSTNode node);

	default T on(final IPSTPreprocessorNode preprocessOrNode) {
		return on((IPSTNode) preprocessOrNode);
	}

	default T on(final IPSTRegularNode node) {
		return on((IPSTNode) node);
	}

	default T on(final IPSTTranslationUnit translationUnit) {
		return on((IPSTRegularNode) translationUnit);
	}
}
