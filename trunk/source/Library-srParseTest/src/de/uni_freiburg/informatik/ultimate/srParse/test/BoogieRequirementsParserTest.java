package de.uni_freiburg.informatik.ultimate.srParse.test;

import java.io.StringReader;
import java.util.Vector;

import java_cup.runtime.Symbol;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import pea.BoogieBooleanExpressionDecision;
import pea.BooleanDecision;
import pea.CDD;
import srParse.ReqLexer;
import srParse.ReqParser;
import srParse.srParsePattern;
import srParse.srParsePattern.PatternType;

public class BoogieRequirementsParserTest {
	
	/**
	 * Use to supply a string (instead of file) to parser.
	 * @param reqFileName
	 * @return
	 * @throws Exception 
	 * 
	 * TODO: i think parentheses using toString at the CDDs is not correct, must be fixed and tests adapted. Translation in boogie is correct anyway
	 */
    private srParsePattern[] GenPatterns(String testInput) throws Exception {
		StringReader sr = new StringReader(testInput);
		ReqLexer lexer = new ReqLexer(sr);
		ReqParser parser = new ReqParser(lexer);
		
		Symbol goal = parser.parse();
		srParsePattern[] patterns = (srParsePattern[]) goal.value;
		
		return patterns;
    }
	
    
    /**
     * Test if single Requirement with comparison and . operator is korrectly parsed
     * @throws Exception
     */
	@Test
	public void TestGlobalInvariantBoogie() throws Exception{
		String testString = "Globally, it is always the case that \"ABC_curr.I >=  BCD_MAX\" holds.";
		srParsePattern[] parsedPatterns = GenPatterns(testString);
		
		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", 
				parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", 
				parsedPatterns[0]);
		Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertEquals("ABC_curr.I >= BCD_MAX", ccds.get(0).toString());
	}
	
    /**
     * Test if single Requirement with comparison and . operator is korrectly parsed
     * @throws Exception
     */
	@Test
	public void TestBooleanLiterals() throws Exception{
		String testString = "Globally, it is always the case that \"true == false\" holds.";
		srParsePattern[] parsedPatterns = GenPatterns(testString);
		
		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", 
				parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", 
				parsedPatterns[0]);
		Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertEquals("true == false", ccds.get(0).toString());
	}
	
	/**
	 * Test if single requirement with comparison, logical operator and calculation is parsed correctly 
	 * @throws Exception
	 */
	@Test
	public void TestGlobalInvariantBoogieComplexExpression() throws Exception{
		String testString = "Globally, it is always the case that \"(ABC_curr >=  BCD_MAX &&"
				+ " diddlidu + 3 == A_bli -3) || a \" holds";
		srParsePattern[] parsedPatterns = GenPatterns(testString);
		
		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", 
				parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", 
				parsedPatterns[0]);
		Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertEquals("(a ∨ ABC_curr >= BCD_MAX ∧ diddlidu + 3 == A_bli - 3)"
				, ccds.get(0).toString(true));
	}
	
	@Test
	public void TestListOfRequirements() throws Exception{
		String testString = 
				"Globally, it is always the case that \"ABC_curr.I >=  BCD_MAX\" holds.\n"+
				"Globally, it is always the case that \"EFG_min >=  X + 3\" holds.\n";
		srParsePattern[] parsedPatterns = GenPatterns(testString);
		
		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", 
				parsedPatterns);
		Assert.assertTrue("Parser did not recognize all Pattern  (2)", 
				parsedPatterns.length == 2);
		Vector<CDD> ccds = parsedPatterns[0].getCdds();
	}
	
	/**
	 * Test if old behaviour is still correctly working
	 * @throws Exception
	 */
	@Test
	public void TestOldBehaviour() throws Exception{
		String testString = "Globally, it is always the case that \"a\" holds";
		srParsePattern[] parsedPatterns = GenPatterns(testString);
		
		System.out.println(parsedPatterns[0].toString());
		Assert.assertNotNull("Parser did not return anything!", 
				parsedPatterns);
		Assert.assertNotNull("Parser did not recognize Global.universal pattern", 
				parsedPatterns[0]);
		Vector<CDD> ccds = parsedPatterns[0].getCdds();
		Assert.assertTrue("Parser did not work on old Requirements with only ap-names",
				ccds.get(0).decision instanceof BooleanDecision);
		System.out.println(ccds.get(0).toString());
	}
	
}



















