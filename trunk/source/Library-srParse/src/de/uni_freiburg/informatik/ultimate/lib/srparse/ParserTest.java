package de.uni_freiburg.informatik.ultimate.lib.srparse;

import java.io.StringReader;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class ParserTest {
	static String scopes[] = { "Globally", "After a", "Before a", "Between a and b", "After a until b" };

	static String patterns[] = { "it is never the case that p holds", "it is always the case that p holds",
			"it is always the case that if p holds and is succeeded by q then r eventually holds after s",
			"it is always the case that if p holds then q holds as well",
			"transitions to states in which p holds occur at most twice", "P eventually holds"
			// "it is always the case that if p holds, then q.x previously held and was preceded by r.x"
	};

	static String test1 =
			"Globally, it is always the case that if p holds, then q.x previously held and was preceded by r.x.\n";

	public void testNewParser(final String input) throws Exception {
		final StringReader sr = new StringReader(input);
		final ReqLexer lexer = new ReqLexer(sr);
		final ReqParser parser = new ReqParser(lexer);

		final Symbol goal = parser.parse();
		final PatternType[] patterns = (PatternType[]) goal.value;

		for (final PatternType pat : patterns) {
			System.out.println(pat);
		}
	}

	public static void main(final String[] param) throws Exception {
		final ParserTest test = new ParserTest();
		for (final String s : scopes) {
			for (final String p : patterns) {
				test.testNewParser(s + ", " + p + ".\n");
			}
		}
	}
}
