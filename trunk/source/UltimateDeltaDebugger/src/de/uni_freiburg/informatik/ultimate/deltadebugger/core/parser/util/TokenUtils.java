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

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.parser.IToken;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;

/**
 * Utilities for tokens.
 */
public final class TokenUtils {
	private TokenUtils() {
		// utility class
	}
	
	/**
	 * @param parentNode
	 *            Parent PST node.
	 * @param expectedTokenTypes
	 *            expected token types
	 * @return array of tokens
	 */
	@SuppressWarnings("squid:S923")
	public static Token[] getExpectedTokenArray(final IPSTNode parentNode, final int... expectedTokenTypes) {
		return TokenUtils.getExpectedTokenArray(TokenCollector.collect(parentNode), expectedTokenTypes);
	}
	
	/**
	 * @param tokens
	 *            List of tokens.
	 * @param expectedTokenTypes
	 *            expected token types
	 * @return array of tokens
	 */
	@SuppressWarnings("squid:S923")
	public static Token[] getExpectedTokenArray(final List<Token> tokens, final int... expectedTokenTypes) {
		final Token[] result = new Token[expectedTokenTypes.length];
		int nextExistingIndex = 0;
		for (int i = 0; i != expectedTokenTypes.length; ++i) {
			final int index = indexOfToken(tokens, nextExistingIndex, expectedTokenTypes[i]);
			if (index != -1) {
				result[i] = tokens.get(index);
				nextExistingIndex = index + 1;
			}
		}
		
		return result;
	}
	
	/**
	 * @param tokens
	 *            List of tokens.
	 * @param tokenType
	 *            token type
	 * @return index of the token
	 */
	public static int indexOfToken(final List<Token> tokens, final int tokenType) {
		return indexOfToken(tokens, 0, tokenType);
	}
	
	/**
	 * @param tokens
	 *            List of tokens.
	 * @param first
	 *            first index
	 * @param tokenType
	 *            token type
	 * @return index of the first token occurrence, -1 if not existent
	 */
	public static int indexOfToken(final List<Token> tokens, final int first, final int tokenType) {
		for (int i = first; i != tokens.size(); ++i) {
			if (tokens.get(i).getType() == tokenType) {
				return i;
			}
		}
		return -1;
	}
	
	/**
	 * @param tokens
	 *            List of tokens.
	 * @return {@code true} iff all parentheses are balanced
	 */
	public static boolean isAllParenthesesBalanced(final List<Token> tokens) {
		final Map<Integer, Long> counts =
				tokens.stream().collect(Collectors.groupingBy(Token::getType, Collectors.counting()));
		if (!counts.getOrDefault(IToken.tLPAREN, 0L).equals(counts.getOrDefault(IToken.tRPAREN, 0L))
				|| !counts.getOrDefault(IToken.tLBRACE, 0L).equals(counts.getOrDefault(IToken.tRBRACE, 0L))
				|| !counts.getOrDefault(IToken.tLBRACKET, 0L).equals(counts.getOrDefault(IToken.tRBRACKET, 0L))) {
			return false;
		}
		return true;
	}
}
