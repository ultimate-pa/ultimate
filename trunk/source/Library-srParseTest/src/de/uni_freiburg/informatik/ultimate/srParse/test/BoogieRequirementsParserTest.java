package de.uni_freiburg.informatik.ultimate.srParse.test;

import java.io.StringReader;
import java.util.Vector;

import org.junit.Assert;
import org.junit.Test;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqLexer;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

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
		final StringReader sr = new StringReader(testInput);
		final ReqLexer lexer = new ReqLexer(sr);
		final ReqParser parser = new ReqParser(lexer);

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
		final String testString = "Globally, it is always the case that \"ABC_curr.I >=  BCD_MAX\" holds.";
		final PatternType[] parsedPatterns = genPatterns(testString);

		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", parsedPatterns[0]);
		final Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertEquals("ABC_curr.I >= BCD_MAX", ccds.get(0).toString());
	}

	/**
	 * Test if single Requirement with comparison and . operator is correctly parsed
	 *
	 * @throws Exception
	 */
	@Test
	public void testBooleanLiterals() throws Exception {
		final String testString = "Globally, it is always the case that \"true == false\" holds.";
		final PatternType[] parsedPatterns = genPatterns(testString);

		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", parsedPatterns[0]);
		final Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertEquals("true == false", ccds.get(0).toString());
	}

	/**
	 * Test if single requirement with comparison, logical operator and calculation is parsed correctly
	 *
	 * @throws Exception
	 */
	@Test
	public void testGlobalInvariantBoogieComplexExpression() throws Exception {
		final String testString = "Globally, it is always the case that \"(ABC_curr >=  BCD_MAX &&"
				+ " diddlidu + 3 == A_bli -3) || a \" holds";
		final PatternType[] parsedPatterns = genPatterns(testString);

		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", parsedPatterns[0]);
		final Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertEquals("(a ∨ ABC_curr >= BCD_MAX ∧ diddlidu + 3 == A_bli - 3)", ccds.get(0).toString(true));
	}

	@Test
	public void testListOfRequirements() throws Exception {
		final String testString = "Globally, it is always the case that \"ABC_curr.I >=  BCD_MAX\" holds.\n"
				+ "Globally, it is always the case that \"EFG_min >=  X + 3\" holds.\n";
		final PatternType[] parsedPatterns = genPatterns(testString);

		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertTrue("Parser did not recognize all Pattern  (2)", parsedPatterns.length == 2);
		final Vector<CDD> ccds = parsedPatterns[0].getCdds();
	}

	/**
	 * Test if old behavior is still correctly working
	 *
	 * @throws Exception
	 */
	// @Test
	public void testOldBehaviour() throws Exception {
		final String testString = "Globally, it is always the case that \"a\" holds";
		final PatternType[] parsedPatterns = genPatterns(testString);

		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", parsedPatterns[0]);
		final Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertTrue("Parser did not work on old Requirements with only ap-names",
				ccds.get(0).decision instanceof BooleanDecision);
		System.out.println(ccds.get(0).toString());
	}

}
