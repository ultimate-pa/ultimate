/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
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
		// utility class
	}
	
	/**
	 * Note: Accesses IASTTranslationUnit to get the LexerOptions.
	 *
	 * @param parentNode
	 *            parent node
	 * @return source range of the token in front
	 */
	public static List<Token> collect(final IPSTNode parentNode) {
		final Visitor instance = new Visitor(parentNode);
		GapVisitor.invokeAccept(parentNode, instance);
		return instance.mResult;
	}
	
	/**
	 * A token.
	 */
	public static class Token implements ISourceRange {
		private final ISourceDocument mSource;
		private final IToken mDelegate;
		
		/**
		 * @param source
		 *            Source document.
		 * @param token
		 *            token
		 */
		public Token(final ISourceDocument source, final IToken token) {
			mSource = source;
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
	
	/**
	 * PST gap visitor.
	 */
	private static final class Visitor implements IPSTGapVisitor {
		private final IPSTNode mParentNode;
		private final ISourceDocument mSource;
		private final List<Token> mResult = new ArrayList<>();
		private LexerOptions mLexerOptions;
		
		private Visitor(final IPSTNode parentNode) {
			mParentNode = parentNode;
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
				mLexerOptions = mParentNode.getTranslationUnit().getAstNode().getAdapter(LexerOptions.class);
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
