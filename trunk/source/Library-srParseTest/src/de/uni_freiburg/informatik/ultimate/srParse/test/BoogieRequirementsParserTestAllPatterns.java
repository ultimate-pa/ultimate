package de.uni_freiburg.informatik.ultimate.srParse.test;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqLexer;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeGlob;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

@RunWith(Parameterized.class)
public class BoogieRequirementsParserTestAllPatterns {

	private final Testpurpose t;

	public BoogieRequirementsParserTestAllPatterns(final Testpurpose t) {
		this.t = t;

	}

	@Test
	public void testPatternParse() throws Exception {
		final PatternType[] parsedPatterns = genPatterns(t.testString);

		Assert.assertNotNull(t.testString, parsedPatterns);
		Assert.assertNotNull("failed parsing: " + t.testString, parsedPatterns[0]);
		Assert.assertTrue("fail recognize: " + t.scopezz.toString() + "[" + t.scopezz + "]:\n" + t.testString,
				parsedPatterns[0].getScope().getClass() == t.scopezz);
		Assert.assertTrue("fail recognize: " + parsedPatterns[0].getClass().toString() + "[" + t.patternName + "]:\n"
				+ t.testString, parsedPatterns[0].getClass().toString().endsWith(t.patternName));
	}

	/**
	 * Use to supply a string (instead of file) to parser.
	 *
	 * @param reqFileName
	 * @return
	 * @throws Exception
	 */
	private PatternType[] genPatterns(final String testInput) throws Exception {
		final StringReader sr = new StringReader(testInput);
		final ReqLexer lexer = new ReqLexer(sr);
		final ReqParser parser = new ReqParser(lexer);

		final Symbol goal = parser.parse();
		final PatternType[] patterns = (PatternType[]) goal.value;

		return patterns;
	}

	/**
	 * Struct transporting data for one test case
	 */
	static class Testpurpose {
		public String testString;
		public Class<?> scopezz;
		public String patternName;

		public Testpurpose(final String testString, final Class<?> scopezz, final String patternName) {
			this.testString = testString;
			this.scopezz = scopezz;
			this.patternName = patternName;
		}
	}

	@Parameters
	public static Collection<Object[]> data() {
		final Collection<Object[]> data = new ArrayList<>();
		// definition of all patterns
		final String[] scope = new String[] { "Globally,", "Before \" x > 0 \", ", "After \" x > 0\", ",
				"Between \"x > 0\" and \" x < 0\", " };
		// TODO?:"After <Q> before <R>"
		final Class<?>[] scopezz = new Class<?>[] { srParseScopeGlob.class, srParseScopeBefore.class,
				srParseScopeAfter.class, srParseScopeBetween.class };

		final String[] pattern = new String[] { "it is never the case that \"y >= 5\" holds.",
				"it is always the case that \"y >= 5\" holds.",
				"transitions to states in which \"y >= 5\" holds occur at most twice",
				"it is always the case that if \"y >= 5\" holds, then \"y <= 5\" previously held",
				// timed
				"it is always the case that once \"y >= 5\" becomes satisfied, it holds for at least 2000 time units",
				"it is always the case that once \"y >= 5\" becomes satisfied, it holds for less than 2000 time units",
				"it is always the case that \"y >= 5\" holds at least every 2000 time units",
				"it is always the case that if \"y >= 5\" holds, then \"y <= 5\" holds after at most 2000 time units",
				"it is always the case that if \"y >= 5\" holds, then \"y <= 5\" holds for at least 2000 time units",
				"it is always the case that after \"y >= 5\" holds for 2000 time units, then \"y <= 5\" holds",
				"it is always the case that if \"y <= 5\" holds then \"y >= 5\" holds as well" };
		final String[] patternNames = new String[] { "InstAbsPattern", "UniversalityPattern", "BndExistencePattern",
				"PrecedencePattern", "MinDurationPattern", "MaxDurationPattern", "BndReccurrencePattern",
				"BndResponsePattern", "BndInvariancePattern", "BndEntryConditionPattern", "InvariantPattern" };

		for (int i = 0; i < scope.length; i++) {
			for (int j = 0; j < pattern.length; j++) {
				final StringBuilder testString = new StringBuilder();
				testString.append(scope[i]);
				testString.append(pattern[j]);
				testString.append(".");
				data.add(new Object[] { new Testpurpose(testString.toString(), scopezz[i], patternNames[j]) });
			}
		}

		return data;
	}

}
