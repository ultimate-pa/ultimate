package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.DefaultParser;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.Parser;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.PSTBuilder;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.StringSourceDocument;

public class DefaultPassContext implements PassContext {
	private final ISourceDocument input;
	private final Parser parser;
	private volatile IASTTranslationUnit ast = null;
	private volatile IPSTTranslationUnit pst = null;

	public DefaultPassContext(final ISourceDocument input) {
		this(input, new DefaultParser());
	}

	public DefaultPassContext(final ISourceDocument input, final Parser parser) {
		this.input = input;
		this.parser = parser;
	}

	public DefaultPassContext(final String input) {
		this(new StringSourceDocument(input));
	}

	public DefaultPassContext(final String input, final Parser parser) {
		this(new StringSourceDocument(input), parser);
	}

	@Override
	public ISourceDocument getInput() {
		return input;
	}

	@Override
	public Parser getParser() {
		return parser;
	}

	@Override
	public IASTTranslationUnit getSharedAST() {
		if (ast == null) {
			synchronized (this) {
				if (ast == null) {
					ast = parser.parse(input.getText());
				}
			}
		}
		return ast;
	}

	@Override
	public IPSTTranslationUnit getSharedPST() {
		if (pst == null) {
			synchronized (this) {
				if (pst == null) {
					pst = new PSTBuilder(getSharedAST(), input).build();
				}
			}
		}
		return pst;
	}

}
