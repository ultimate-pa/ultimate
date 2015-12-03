package de.uni_freiburg.informatik.ultimate.PEATestTransformerTest.Transfromer;

import java.awt.List;
import java.util.ArrayList;
import java.util.Vector;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.PatternToPea;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.PhaseEventAutomata;
import srParse.srParseScopeGlob;
import srParse.pattern.InstAbsPattern;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;

/**
 * Positive test for all automata translations
 * TODO: for ALL
 * @author Langenfeld
 *
 */
public class PatternToPeaTest {
	
	private PatternToPea transformer = new PatternToPea();

	@Test
	public void GlobalInstAbsPatternTest(){
		//setup
		PatternType pattern = new InstAbsPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		cdd.add(BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b")));
		pattern.mergeCDDs(cdd);	
		pattern.setScope(new srParseScopeGlob());
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 1 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Phases", 1 , pea.getPhases()[0].getTransitions().size());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		Assert.assertEquals("Edge guard is wrong", "TRUE", 
				pea.getPhases()[0].getTransitions().get(0).getGuard().toString());
		Assert.assertEquals("Phase invariant is wrong", "!(a == b)", 
				pea.getPhases()[0].getStateInvariant().toString());
	}
	
	@Test
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
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 1 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Phases", 1 , pea.getPhases()[0].getTransitions().size());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		Assert.assertEquals("Edge guard is wrong", "TRUE", 
				pea.getPhases()[0].getTransitions().get(0).getGuard().toString());
		Assert.assertEquals("Phase invariant is wrong", "c == d ∨ !(a == b)", 
				pea.getPhases()[0].getStateInvariant().toString());
	}
	
	
}