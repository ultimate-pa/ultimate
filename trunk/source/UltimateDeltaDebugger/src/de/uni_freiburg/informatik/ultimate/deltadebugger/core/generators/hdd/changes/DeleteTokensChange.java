package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public class DeleteTokensChange extends Change {
	private final List<Token> tokens;

	public DeleteTokensChange(final IPSTNode node, final List<Token> tokens) {
		super(node);
		this.tokens = tokens;
	}

	@Override
	public void apply(final SourceRewriter rewriter) {
		for (final ISourceRange location : tokens) {
			replaceByWhitespace(rewriter, location);
		}
	}

	@Override
	public String toString() {
		return "Delete tokens from " + getNode() + ": " + tokens;
	}

}