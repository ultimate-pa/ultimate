package de.uni_freiburg.informatik.ultimate.srParse.test;

import java.io.StringReader;
import java.util.List;

import org.hamcrest.core.Is;
import org.junit.Assert;
import org.junit.Test;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqLexer;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class BoogieRequirementsParserTest {

	/**
	 * Use to supply a string (instead of file) to parser.
	 *
	 * @param reqFileName
	 * @return
	 * @throws Exception
	 *
	 */
	private PatternType[] genPatterns(final String testInput) throws Exception {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();

		final StringReader sr = new StringReader(testInput);
		final ReqLexer lexer = new ReqLexer(sr);
		final ReqParser parser = new ReqParser(services, services.getLoggingService().getLogger(getClass()), lexer);
		final Symbol goal = parser.parse();
		final PatternType[] patterns = (PatternType[]) goal.value;

		return patterns;
	}

	/**
	 * Test if single Requirement with comparison and . operator is korrectly parsed
	 *
	 * @throws Exception
	 */
	@Test
	public void testGlobalInvariantBoogie() throws Exception {
		final String testString = "id: Globally, it is always the case that \"ABC_curr.I >=  BCD_MAX\" holds.";
		final PatternType[] parsedPatterns = genPatterns(testString);
		check(parsedPatterns, "ABC_curr.I >= BCD_MAX");
	}

	private static void check(final PatternType[] parsedPatterns, final String cddCheck) {
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertThat(parsedPatterns.length, Is.is(1));
		final PatternType thePattern = parsedPatterns[0];
		Assert.assertNotNull("Parser did not recognize pattern", thePattern);
		final List<CDD> ccds = thePattern.getCdds();
		Assert.assertEquals(cddCheck, ccds.get(0).toString());
		System.out.println(thePattern.toString());
	}

	/**
	 * Test if single Requirement with comparison and . operator is correctly parsed
	 *
	 * @throws Exception
	 */
	@Test
	public void testBooleanLiterals() throws Exception {
		final String testString = "id: Globally, it is always the case that \"true == false\" holds.";
		final PatternType[] parsedPatterns = genPatterns(testString);
		check(parsedPatterns, "true == false");
	}

	/**
	 * Test if single requirement with comparison, logical operator and calculation is parsed correctly
	 *
	 * @throws Exception
	 */
	@Test
	public void testGlobalInvariantBoogieComplexExpression() throws Exception {
		final String testString = "id: Globally, it is always the case that \"(ABC_curr >=  BCD_MAX &&"
				+ " diddlidu + 3 == A_bli -3) || a \" holds";
		final PatternType[] parsedPatterns = genPatterns(testString);
		check(parsedPatterns, "a ∨ ABC_curr >= BCD_MAX ∧ diddlidu + 3 == A_bli - 3");
	}

	@Test
	public void testListOfRequirements() throws Exception {
		final String testString = "id1: Globally, it is always the case that \"ABC_curr.I >=  BCD_MAX\" holds.\n"
				+ "id2: Globally, it is always the case that \"EFG_min >=  X + 3\" holds.\n";
		final PatternType[] parsedPatterns = genPatterns(testString);

		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertTrue("Parser did not recognize all Pattern  (2)", parsedPatterns.length == 2);
		System.out.println(parsedPatterns[0].toString());
		System.out.println(parsedPatterns[1].toString());
	}

	/**
	 * Test if old behavior is still correctly working
	 *
	 * @throws Exception
	 */
	// @Test
	public void testOldBehaviour() throws Exception {
		final String testString = "id: Globally, it is always the case that \"a\" holds";
		final PatternType[] parsedPatterns = genPatterns(testString);

		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", parsedPatterns[0]);
		final List<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertTrue("Parser did not work on old Requirements with only ap-names",
				ccds.get(0).decision instanceof BooleanDecision);
		System.out.println(ccds.get(0).toString());
	}

}
