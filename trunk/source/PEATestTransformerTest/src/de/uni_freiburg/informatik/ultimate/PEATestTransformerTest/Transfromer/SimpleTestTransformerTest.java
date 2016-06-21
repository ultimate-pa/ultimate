package de.uni_freiburg.informatik.ultimate.PEATestTransformerTest.Transfromer;

import java.util.ArrayList;
import java.util.Vector;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.NullTransformer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.SimplePositiveTestTransformer;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.PhaseEventAutomata;
import srParse.srParseScopeGlob;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;

public class SimpleTestTransformerTest {
	
	private SimplePositiveTestTransformer transformer; 
	private SystemInformation sysInfo;
	
	@Before
	public void SetUp(){
		sysInfo = new SystemInformation();
		transformer = new SimplePositiveTestTransformer(sysInfo);
	}
	
	@Test
	public void GlobalInvariantTrapTest(){
		//setup
		PatternType pattern = new InvariantPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		//this works in reverse order so result down below is right!
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		CDD	p = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("g", "h"));
		cdd.add(s);
		cdd.add(p);
		pattern.mergeCDDs(cdd);	
		pattern.setScope(new srParseScopeGlob());
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 2, pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());

	}

}
