package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collection;

import org.hamcrest.core.Is;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

@RunWith(Parameterized.class)
public class BoogieRequirementsParserTestAllPatterns {

	private final Testpurpose mActualTest;

	public BoogieRequirementsParserTestAllPatterns(final Testpurpose purpose) {
		mActualTest = purpose;

	}

	@Test
	public void testPatternParse() throws Exception {
		final PatternType[] parsedPatterns = genPatterns(mActualTest.mTestString);
		Assert.assertNotNull("Pattern is null", parsedPatterns);
		Assert.assertThat("Is not only one pattern", parsedPatterns.length, Is.is(1));
		Assert.assertNotNull("Failed parsing: " + mActualTest.mTestString, parsedPatterns[0]);
		Assert.assertTrue("Fail recognize: " + mActualTest.mScopeClazz.toString() + "[" + mActualTest.mScopeClazz
				+ "]:\n" + mActualTest.mTestString, parsedPatterns[0].getScope().getClass() == mActualTest.mScopeClazz);
		Assert.assertTrue(
				"fail recognize: " + parsedPatterns[0].getClass().toString() + "[" + mActualTest.mPatternName + "]:\n"
						+ mActualTest.mTestString,
				parsedPatterns[0].getClass().toString().endsWith(mActualTest.mPatternName));
	}

	/**
	 * Use to supply a string (instead of file) to parser.
	 *
	 * @param reqFileName
	 * @return
	 * @throws Exception
	 */
	private PatternType[] genPatterns(final String testInput) throws Exception {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		final StringReader sr = new StringReader(testInput);
		final ReqParser parser = new ReqParser(services, services.getLoggingService().getLogger(getClass()), sr, "");

		final Symbol goal = parser.parse();
		final PatternType[] patterns = (PatternType[]) goal.value;

		return patterns;
	}

	@Parameters(name = "{index}: {0}")
	public static Collection<Object[]> data() {
		final Collection<Object[]> data = new ArrayList<>();
		// definition of all patterns
		final String[] scope = new String[] { "Globally,", "Before \" x > 0 \", ", "After \" x > 0\", ",
				"Between \"x > 0\" and \" x < 0\", " };
		// TODO?:"After <Q> before <R>"
		final Class<?>[] scopezz = new Class<?>[] { SrParseScopeGlob.class, SrParseScopeBefore.class,
				SrParseScopeAfter.class, SrParseScopeBetween.class };

		final String[] pattern = new String[] { "it is never the case that \"y >= 5\" holds",
				"it is always the case that \"y >= 5\" holds",
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
				"BndResponsePatternUT", "BndInvariancePattern", "BndEntryConditionPattern", "InvariantPattern" };

		for (int i = 0; i < scope.length; i++) {
			for (int j = 0; j < pattern.length; j++) {
				final StringBuilder testString = new StringBuilder();
				testString.append("id_");
				testString.append(String.valueOf(i));
				testString.append("_");
				testString.append(String.valueOf(j));
				testString.append(": ");
				testString.append(scope[i]);
				testString.append(pattern[j]);
				testString.append(".");
				data.add(new Object[] { new Testpurpose(testString.toString(), scopezz[i], patternNames[j]) });
			}
		}

		return data;
	}

	/**
	 * Struct transporting data for one test case
	 */
	private static final class Testpurpose {
		public final String mTestString;
		public final Class<?> mScopeClazz;
		public final String mPatternName;

		public Testpurpose(final String testString, final Class<?> scopezz, final String patternName) {
			mTestString = testString;
			mScopeClazz = scopezz;
			mPatternName = patternName;
		}

		@Override
		public String toString() {
			return mPatternName;
		}
	}

}
