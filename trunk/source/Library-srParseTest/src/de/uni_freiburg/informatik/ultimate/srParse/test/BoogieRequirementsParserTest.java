package de.uni_freiburg.informatik.ultimate.srParse.test;

import java.io.StringReader;
import java.util.Vector;

import org.junit.Assert;
import org.junit.Test;

import java_cup.runtime.Symbol;
import pea.BooleanDecision;
import pea.CDD;
import srParse.ReqLexer;
import srParse.ReqParser;
import srParse.pattern.PatternType;

public class BoogieRequirementsParserTest {
	
	/**
	 * Use to supply a string (instead of file) to parser.
	 * @param reqFileName
	 * @return
	 * @throws Exception 
	 * 
	*/
    private PatternType[] GenPatterns(String testInput) throws Exception {
		StringReader sr = new StringReader(testInput);
		ReqLexer lexer = new ReqLexer(sr);
		ReqParser parser = new ReqParser(lexer);
		
		Symbol goal = parser.parse();
		PatternType[] patterns = (PatternType[]) goal.value;
		
		return patterns;
    }
	
    
    /**
     * Test if single Requirement with comparison and . operator is korrectly parsed
     * @throws Exception
     */
	@Test
	public void TestGlobalInvariantBoogie() throws Exception{
		String testString = "Globally, it is always the case that \"ABC_curr.I >=  BCD_MAX\" holds.";
		PatternType[] parsedPatterns = GenPatterns(testString);
		
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
		PatternType[] parsedPatterns = GenPatterns(testString);
		
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
		PatternType[] parsedPatterns = GenPatterns(testString);
		
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
		PatternType[] parsedPatterns = GenPatterns(testString);
		
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
	//@Test
	public void TestOldBehaviour() throws Exception{
		String testString = "Globally, it is always the case that \"a\" holds";
		PatternType[] parsedPatterns = GenPatterns(testString);
		
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



















