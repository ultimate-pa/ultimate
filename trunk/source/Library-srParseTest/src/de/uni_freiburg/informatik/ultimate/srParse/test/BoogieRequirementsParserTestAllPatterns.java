package de.uni_freiburg.informatik.ultimate.srParse.test;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import java_cup.runtime.Symbol;
import srParse.ReqLexer;
import srParse.ReqParser;
import srParse.srParseScopeAfter;
import srParse.srParseScopeBefore;
import srParse.srParseScopeBetween;
import srParse.srParseScopeGlob;
import srParse.pattern.PatternType;

@RunWith(Parameterized.class)
public class BoogieRequirementsParserTestAllPatterns {
    
    private Testpurpose t;
   
    public BoogieRequirementsParserTestAllPatterns(Testpurpose t){
    	this.t = t;

    }
    
	@Test
	public void TestPatternParse() throws Exception{
		PatternType[] parsedPatterns = GenPatterns(this.t.testString);
		
		Assert.assertNotNull( this.t.testString, parsedPatterns);
		Assert.assertNotNull("failed parsing: "+this.t.testString,
				parsedPatterns[0]);
		Assert.assertTrue("fail recognize: "+ this.t.scopezz.toString() + "["+this.t.scopezz+"]:\n"+this.t.testString,
				parsedPatterns[0].getScope().getClass() == this.t.scopezz);
		Assert.assertTrue("fail recognize: "+ parsedPatterns[0].getClass().toString()
				+ "["+this.t.patternName+"]:\n"+this.t.testString,
				parsedPatterns[0].getClass().toString().endsWith(this.t.patternName));
	}
	
	/**
	 * Use to supply a string (instead of file) to parser.
	 * @param reqFileName
	 * @return
	 * @throws Exception 
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
	 * Struct transporting data for one test case
	 */
	static class Testpurpose{
		public String testString;
		public Class<?> scopezz;
		public String patternName;
		public Testpurpose(String testString, Class<?> scopezz, String patternName){
			this.testString = testString;
			this.scopezz = scopezz;
			this.patternName = patternName;
		}
	}
	
    @Parameters
    public static Collection<Object[]> data() {
        Collection<Object[]> data = new ArrayList<Object[]>();
    	//definition of all patterns
		String[] scope = new String[]{
				"Globally,",
				"Before \" x > 0 \", ",
				"After \" x > 0\", ",
				"Between \"x > 0\" and \" x < 0\", "};
				//TODO?:"After <Q> before <R>"
		Class<?>[] scopezz = new Class<?>[]{
				srParseScopeGlob.class,
				srParseScopeBefore.class,
				srParseScopeAfter.class,
				srParseScopeBetween.class};
		
		
		String[] pattern = new String[]{
			"it is never the case that \"y >= 5\" holds.",
			"it is always the case that \"y >= 5\" holds.",
			"transitions to states in which \"y >= 5\" holds occur at most twice",
			"it is always the case that if \"y >= 5\" holds, then \"y <= 5\" previously held",
			//timed
			"it is always the case that once \"y >= 5\" becomes satisfied, it holds for at least 2000 time units",
			"it is always the case that once \"y >= 5\" becomes satisfied, it holds for less than 2000 time units",
			"it is always the case that \"y >= 5\" holds at least every 2000 time units",
			"it is always the case that if \"y >= 5\" holds, then \"y <= 5\" holds after at most 2000 time units",
			"it is always the case that if \"y >= 5\" holds, then \"y <= 5\" holds for at least 2000 time units",
			"it is always the case that after \"y >= 5\" holds for 2000 time units, then \"y <= 5\" holds",
			"it is always the case that if \"y <= 5\" holds then \"y >= 5\" holds as well"
		};
		String[] patternNames = new String[]{
				"InstAbsPattern",
				"UniversalityPattern",
				"BndExistencePattern",
				"PrecedencePattern",
				"MinDurationPattern",
				"MaxDurationPattern",
				"BndReccurrencePattern",
				"BndResponsePattern",
				"BndInvariancePattern",
				"BndEntryConditionPattern",
				"InvariantPattern"
			};
		
		for(int i = 0; i < scope.length; i++){
			for(int j = 0; j < pattern.length; j++){
				StringBuilder testString = new StringBuilder();
				testString.append(scope[i]);
				testString.append(pattern[j]);
				testString.append(".");
				data.add(new Object[]{new Testpurpose(testString.toString(), scopezz[i], patternNames[j])});
			}
		}
		
        return data;
    }
	
	
	

}
