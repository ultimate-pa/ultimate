package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.Parser;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * A pass context provides the (immutable) input to a variant generator.
 *
 * Important: The observable state of the context and the returned objects must
 * not be changed, because they may be shared with other passes.
 * 
 * It exists mainly to prevent redundant parsing of the same input for multiple
 * passes, if there are no successful modifications in between. Global options
 * that affect a passes algorithm should eventually also go in here.
 */
public interface PassContext {

	/**
	 * @return the input source code document
	 */
	ISourceDocument getInput();

	/**
	 * @return the parser to be used for manual parsing
	 */
	Parser getParser();

	/**
	 * Returns a lazily computed and internally cached AST instance for the
	 * input source code. This AST instance is shared with subsequent passes if
	 * no change is possible.
	 * 
	 * @return the AST created with default options from the input source
	 */
	IASTTranslationUnit getSharedAST();

	/**
	 * Returns a lazily computed and internally cached APT instance for the
	 * input source code and the shared AST. This PST instance is shared with
	 * subsequent passes if no change is possible.
	 * 
	 * Note that the returned instance must not be modified to not affect other
	 * passes.
	 * 
	 * @return the PST created with default options from the shared AST
	 */
	IPSTTranslationUnit getSharedPST();
}