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
public final class TokenCollector {

	private static final CharArrayIntMap keywords;

	private static final int INITIAL_KEYWORD_MAP_SIZE = 40;

	static {
		keywords = new CharArrayIntMap(INITIAL_KEYWORD_MAP_SIZE, -1);
		Keywords.addKeywordsC(keywords);
	}

	private TokenCollector() {
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
		return instance.mResult;
	}

	public static class Token implements ISourceRange {
		private final ISourceDocument mSource;
		private final IToken mDelegate;

		public Token(final ISourceDocument source, final IToken token) {
			this.mSource = source;
			mDelegate = token;
		}

		@Override
		public int endOffset() {
			return mDelegate.getEndOffset();
		}

		public char[] getCharImage() {
			return mDelegate.getCharImage();
		}

		public String getImage() {
			return mDelegate.getImage();
		}

		public ISourceDocument getSource() {
			return mSource;
		}

		public int getType() {
			return mDelegate.getType();
		}

		@Override
		public int offset() {
			return mDelegate.getOffset();
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("Token (\"").append(getImage()).append("\") ")
					.append(mSource.newSourceRange(offset(), endOffset()));
			return sb.toString();
		}

	}

	private static final class Visitor implements IPSTGapVisitor {
		private final IPSTNode mParentNode;
		private final ISourceDocument mSource;
		private final List<Token> mResult = new ArrayList<>();
		private LexerOptions mLexerOptions;

		private Visitor(final IPSTNode parentNode) {
			this.mParentNode = parentNode;
			mSource = parentNode.getSource();
		}

		private void addTokens(final int offset, final int endOffset) {
			final String text = mSource.getText(offset, endOffset);
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
			if (node.equals(mParentNode) || node instanceof IPSTConditionalBlock) {
				return PROCESS_CONTINUE;
			}
			return PROCESS_SKIP;
		}

		private LexerOptions getLexerOptions() {
			if (mLexerOptions == null) {
				mLexerOptions = mParentNode.getTranslationUnit().getASTNode().getAdapter(LexerOptions.class);
			}
			return mLexerOptions;
		}

		private void runLexer(final String text, final int offset) throws OffsetLimitReachedException {
			final Lexer lexer = new Lexer(text.toCharArray(), getLexerOptions(), ILexerLog.NULL, null);
			while (true) {
				final org.eclipse.cdt.internal.core.parser.scanner.Token token = lexer.nextToken();
				final int kind = token.getType();
				if (kind == IToken.tEND_OF_INPUT) {
					return;
				}
				if (kind == Lexer.tNEWLINE) {
					continue;
				}
				if (kind == IToken.tIDENTIFIER) {
					final int tokenType = keywords.get(token.getCharImage());
					if (tokenType != keywords.undefined) {
						token.setType(tokenType);
					}
				}
				token.setOffset(offset + token.getOffset(), offset + token.getEndOffset());
				mResult.add(new Token(mSource, token));
			}
		}

		@Override
		public int visitGap(final int offset, final int endOffset) {
			addTokens(offset, endOffset);
			return PROCESS_CONTINUE;
		}
	}

}
