package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.parser.IToken;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;

public final class TokenUtils {

	private TokenUtils() {

	}
	
	public static Token[] getExpectedTokenArray(final IPSTNode parentNode, final int... expectedTokenTypes) {
		return TokenUtils.getExpectedTokenArray(TokenCollector.collect(parentNode), expectedTokenTypes);
	}

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

	public static int indexOfToken(final List<Token> tokens, final int tokenType) {
		return indexOfToken(tokens, 0, tokenType);
	}

	public static int indexOfToken(final List<Token> tokens, final int first, final int tokenType) {
		for (int i = first; i != tokens.size(); ++i) {
			if (tokens.get(i).getType() == tokenType) {
				return i;
			}
		}
		return -1;
	}

	public static boolean isAllParenthesisBalanced(final List<Token> tokens) {
		final Map<Integer, Long> counts =
				tokens.stream().collect(Collectors.groupingBy(Token::getType, Collectors.counting()));
		if (counts.getOrDefault(IToken.tLPAREN, 0L) != counts.getOrDefault(IToken.tRPAREN, 0L)
				|| counts.getOrDefault(IToken.tLBRACE, 0L) != counts.getOrDefault(IToken.tRBRACE, 0L)
				|| counts.getOrDefault(IToken.tLBRACKET, 0L) != counts.getOrDefault(IToken.tRBRACKET, 0L)) {
			return false;
		}
		return true;
	}

}
