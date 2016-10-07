package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.model.ILanguage;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Simplified Parser interface to remove configuration and boilerplate from variant generators. Ensures a consistent
 * parser configuration and default settings.
 */
public interface Parser {
	IPSTTranslationUnit createPST(IASTTranslationUnit ast, ISourceDocument sourceDocument);

	/**
	 * Parse a source code from string and create a new AST instance.
	 *
	 * Default options are {@link ILanguage#OPTION_IS_SOURCE_UNIT} and {@link ILanguage#OPTION_NO_IMAGE_LOCATIONS} The
	 * most interesting additional option should be {@link ILanguage#OPTION_SKIP_FUNCTION_BODIES} to speed up the
	 * parsing.
	 *
	 * @param source
	 *            source code string
	 * @return new AST instance
	 */
	IASTTranslationUnit parse(String source);

	/**
	 * Parse a source code from string and create a new AST instance.
	 *
	 * @see org.eclipse.cdt.core.model.ILanguage for possible options
	 *
	 * @param source
	 *            source code string
	 * @param options
	 * @return new AST instance
	 */
	IASTTranslationUnit parse(String source, int options);
}