package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.StringReader;
import java.util.Collection;
import java.util.stream.Collectors;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.Is;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.PatternUtil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

@RunWith(Parameterized.class)
public class ParseAllPatternsTestsuite {

	private final PatternType<?> mActualTest;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	public ParseAllPatternsTestsuite(final PatternType<?> pattern, final String name) {
		mActualTest = pattern;
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger(getClass());

	}

	@SuppressWarnings("unchecked")
	@Test
	public void testPatternParse() throws Exception {
		final String input = mActualTest.toString();
		final Class<? extends SrParseScope<?>> scopeClazz =
				(Class<? extends SrParseScope<?>>) mActualTest.getScope().getClass();
		final Class<? extends PatternType<?>> patternClazz = (Class<? extends PatternType<?>>) mActualTest.getClass();

		mLogger.info(patternClazz);
		mLogger.info("Parsing: %s", input);
		final PatternType<?>[] parsedPatterns = genPatterns(input);
		final String output;
		if (parsedPatterns != null && parsedPatterns[0] != null) {
			output = parsedPatterns[0].toString();
		} else {
			output = null;
		}
		mLogger.info("Parsed:  %s", output);
		mLogger.info("--");

		Assert.assertNotNull("Parser returned null", parsedPatterns);
		MatcherAssert.assertThat("Is not only one pattern", parsedPatterns.length, Is.is(1));
		Assert.assertNotNull("Parser returned null pattern", parsedPatterns[0]);

		Assert.assertTrue("Parsed wrong scope", parsedPatterns[0].getScope().getClass() == scopeClazz);
		Assert.assertTrue("Parsed wrong pattern type", parsedPatterns[0].getClass() == patternClazz);
		Assert.assertTrue("Roundtrip failed", input.equals(output));
	}

	/**
	 * Use to supply a string (instead of file) to parser.
	 */
	private PatternType<?>[] genPatterns(final String testInput) throws Exception {
		final StringReader sr = new StringReader(testInput);
		final ReqParser parser = new ReqParser(mLogger, sr, "");

		final Symbol goal = parser.parse();
		final PatternType<?>[] patterns = (PatternType<?>[]) goal.value;

		return patterns;
	}

	@Parameters(name = "{1}")
	public static Collection<Object[]> data() {
		return PatternUtil.createAllPatterns(false).getFirst().stream().map(ParseAllPatternsTestsuite::toData)
				.collect(Collectors.toList());
	}

	public static Object[] toData(final PatternType<?> pattern) {
		final String name = String.format("%s_%s", pattern.getClass().getSimpleName(),
				pattern.getScope().getClass().getSimpleName());
		return new Object[] { pattern, name };
	}

}
