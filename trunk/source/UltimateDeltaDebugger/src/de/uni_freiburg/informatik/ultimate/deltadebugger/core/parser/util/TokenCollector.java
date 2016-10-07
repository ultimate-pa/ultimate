package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.parser.IToken;
import org.eclipse.cdt.core.parser.Keywords;
import org.eclipse.cdt.core.parser.OffsetLimitReachedException;
import org.eclipse.cdt.core.parser.util.CharArrayIntMap;
import org.eclipse.cdt.internal.core.parser.scanner.ILexerLog;
import org.eclipse.cdt.internal.core.parser.scanner.Lexer;
import org.eclipse.cdt.internal.core.parser.scanner.Lexer.LexerOptions;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTGapVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * Utility class to collect tokens between child nodes.
 *
 * Implementation notes: By checking the "gaps" in the PST we can easily find tokens between nodes without preprocessing
 * the source text. Only requirement is that all preprocessor directives and comments actually exist in the PST.
 */
@SuppressWarnings("restriction")
public class TokenCollector {
	public static class Token implements ISourceRange {
		final ISourceDocument source;
		final IToken delegate;

		public Token(final ISourceDocument source, final IToken token) {
			this.source = source;
			delegate = token;
		}

		@Override
		public int endOffset() {
			return delegate.getEndOffset();
		}

		public char[] getCharImage() {
			return delegate.getCharImage();
		}

		public String getImage() {
			return delegate.getImage();
		}

		public ISourceDocument getSource() {
			return source;
		}

		public int getType() {
			return delegate.getType();
		}

		@Override
		public int offset() {
			return delegate.getOffset();
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("Token (\"").append(getImage()).append("\") ")
					.append(source.newSourceRange(offset(), endOffset()));
			return sb.toString();
		}

	}

	private static class Visitor implements IPSTGapVisitor {
		private final IPSTNode parentNode;
		private final ISourceDocument source;
		private final List<Token> result = new ArrayList<>();
		private LexerOptions lexerOptions = null;

		private Visitor(final IPSTNode parentNode) {
			this.parentNode = parentNode;
			source = parentNode.getSource();
		}

		private void addTokens(final int offset, final int endOffset) {
			final String text = source.getText(offset, endOffset);
			if (text.trim().isEmpty()) {
				return;
			}
			try {
				runLexer(text, offset);
			} catch (final OffsetLimitReachedException e) {
				// Does not happen without using content assist limit.
			}
		}

		@Override
		public int defaultVisit(final IPSTNode node) {
			if (node == parentNode || node instanceof IPSTConditionalBlock) {
				return PROCESS_CONTINUE;
			}
			return PROCESS_SKIP;
		}

		private LexerOptions getLexerOptions() {
			if (lexerOptions == null) {
				lexerOptions = parentNode.getTranslationUnit().getASTNode().getAdapter(LexerOptions.class);
			}
			return lexerOptions;
		}

		private void runLexer(final String text, final int offset) throws OffsetLimitReachedException {
			final Lexer lexer = new Lexer(text.toCharArray(), getLexerOptions(), ILexerLog.NULL, null);
			while (true) {
				final org.eclipse.cdt.internal.core.parser.scanner.Token token = lexer.nextToken();
				switch (token.getType()) {
				case IToken.tEND_OF_INPUT:
					return;
				case Lexer.tNEWLINE:
					break;
				case IToken.tIDENTIFIER:
					final int tokenType = keywords.get(token.getCharImage());
					if (tokenType != keywords.undefined) {
						token.setType(tokenType);
					}
				default:
					token.setOffset(offset + token.getOffset(), offset + token.getEndOffset());
					result.add(new Token(source, token));
					break;
				}
			}
		}

		@Override
		public int visitGap(final int offset, final int endOffset) {
			addTokens(offset, endOffset);
			return PROCESS_CONTINUE;
		}
	}

	private static final CharArrayIntMap keywords;

	static {
		keywords = new CharArrayIntMap(40, -1);
		Keywords.addKeywordsC(keywords);
	}

	/**
	 * Note: Accesses IASTTranslationUnit to get the LexerOptions.
	 *
	 * @param parentNode
	 *            parent node
	 * @param childNode
	 *            child node
	 * @return source range of the token in front
	 */
	public static List<Token> collect(final IPSTNode parentNode) {
		final Visitor instance = new Visitor(parentNode);
		GapVisitor.invokeAccept(parentNode, instance);
		return instance.result;
	}

	private TokenCollector() {
	}

}
