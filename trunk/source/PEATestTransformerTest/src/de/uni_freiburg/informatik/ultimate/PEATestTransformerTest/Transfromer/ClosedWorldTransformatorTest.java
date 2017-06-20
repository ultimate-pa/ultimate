package de.uni_freiburg.informatik.ultimate.PEATestTransformerTest.Transfromer;

import java.util.ArrayList;
import java.util.Vector;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.ClosedWorldTransformator;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.PhaseEventAutomata;
import srParse.srParseScopeGlob;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;

public class ClosedWorldTransformatorTest {
	
	private ClosedWorldTransformator transformer;

	@Before
	public void SetUp(){
		this.transformer = new ClosedWorldTransformator(new SystemInformation());
	}
	
	@Test
	// (a == b) -> (c == d)
	public void GlobalInvariantPatternTest(){
		//setup
		PatternType pattern = new InvariantPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		//this works in reverse order so result down below is right!
		cdd.add(BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("c", "d")));
		cdd.add(BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b")));
		pattern.mergeCDDs(cdd);	
		pattern.setScope(new srParseScopeGlob());
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = this.transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 1 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Phases", 2 , pea.getPhases()[0].getTransitions().size());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		Assert.assertEquals("Edge guard is wrong", "!R_1_d ∧ !R_1_c ∧ a == b", 
				pea.getPhases()[0].getTransitions().get(0).getGuard().toString());
		Assert.assertEquals("Edge guard is wrong", "!(a == b)", 
				pea.getPhases()[0].getTransitions().get(1).getGuard().toString());
		Assert.assertEquals("Phase invariant is wrong", "c == d ∨ !(a == b)", 
				pea.getPhases()[0].getStateInvariant().toString());
	}

}
