package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.StringReader;
import java.util.List;

import org.hamcrest.core.Is;
import org.junit.Assert;
import org.junit.Test;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
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
		final ReqParser parser = new ReqParser(services, services.getLoggingService().getLogger(getClass()), sr, "");
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
		final String testString = "id: Globally, it is always the case that \"A >=  B\" holds.";
		check(testString, "A >= B");
	}

	/**
	 * Test if single Requirement with comparison and . operator is correctly parsed
	 *
	 * @throws Exception
	 */
	@Test
	public void testBooleanLiterals() throws Exception {
		final String testString = "id: Globally, it is always the case that \"true == false\" holds.";
		check(testString, "true == false");
	}

	/**
	 * Test if single requirement with comparison, logical operator and calculation is parsed correctly
	 *
	 * @throws Exception
	 */
	@Test
	public void testGlobalInvariantBoogieComplexExpression() throws Exception {
		final String testString =
				"id: Globally, it is always the case that \"(A >= B &&" + " C + 3 == D -3) || E \" holds";
		check(testString, "((A >= B ∧ (C + 3 == D - 3 ∨ E)) ∨ E)");
	}

	@Test
	public void testListOfRequirements() throws Exception {
		final String testString = "id1: Globally, it is always the case that \"A >=  B\" holds.\n"
				+ "id2: Globally, it is always the case that \"C >= D + 3\" holds.\n";
		final PatternType[] parsedPatterns = genPatterns(testString);

		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertTrue("Parser did not recognize all Pattern (2)", parsedPatterns.length == 2);
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
		final String testString = "id: Globally, it is always the case that \"A\" holds";
		final PatternType[] parsedPatterns = genPatterns(testString);

		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", parsedPatterns[0]);
		final List<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertTrue("Parser did not work on old Requirements with only ap-names",
				ccds.get(0).getDecision() instanceof BooleanDecision);
		System.out.println(ccds.get(0).toString());
	}

	@Test
	public void orAndNested() throws Exception {
		final String testString =
				"id: Globally, it is always the case that \"A == 0 && (B == 0 || !C || B == 1)\" holds";
		check(testString, "(A == 0 ∧ (B == 0 ∨ (B == 1 ∨ !C)))");
	}

	private void check(final String testString, final String cddCheck) throws Exception {
		final PatternType[] parsedPatterns = genPatterns(testString);
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertThat(parsedPatterns.length, Is.is(1));
		final PatternType pattern = parsedPatterns[0];
		Assert.assertNotNull("Parser did not recognize pattern", pattern);
		final List<CDD> cdds = pattern.getCdds();
		Assert.assertThat(cdds.size(), Is.is(1));
		final CDD cdd = cdds.get(0);

		System.out.println(testString);
		System.out.println("Should: " + cddCheck);
		System.out.println("Is:     " + cdd.toString());
		Assert.assertEquals(cddCheck, cdd.toString());
	}

}
