package de.uni_freiburg.informatik.ultimate.PEATestTransformerTest.Transfromer;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.NullTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;
import srParse.srParseScopeAfter;
import srParse.srParseScopeAfterUntil;
import srParse.srParseScopeBefore;
import srParse.srParseScopeBetween;
import srParse.srParseScopeGlob;
import srParse.pattern.BndResponsePattern;
import srParse.pattern.InstAbsPattern;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;

/**
 * Positive test for all automata translations
 * TODO: for ALL
 * @author Langenfeld
 *
 */
public class BasicTransformerTest {
	
	private NullTransformer transformer = new NullTransformer();
	
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
	public void GlobalBndResponsePatternTest(){
		//setup
		PatternType pattern = new BndResponsePattern();
		Vector<CDD> cdd = new Vector<CDD>();
		//this works in reverse order so result down below is right!
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		CDD	p = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("g", "h"));
		cdd.add(p);
		cdd.add(s);
		pattern.mergeCDDs(cdd);	
		CDD r = BoogieBooleanExpressionDecision.create(
				BoogieAstSnippet.createBooleanExpression("e", "f"));
		CDD q = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("c", "d"));
		pattern.setScope(new srParseScopeGlob());
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 3 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Clocks", 1 , pea.getClocks().size());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st0"), s.or(p.negate()));
	}
	
	@Test
	public void BeforeInvariantPatternTest(){
		//setup
		PatternType pattern = new InvariantPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		//this works in reverse order so result down below is right!
		CDD p = BoogieBooleanExpressionDecision 
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		cdd.add(p);
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("c", "d"));
		cdd.add(s);
		pattern.mergeCDDs(cdd);	
		CDD r = BoogieBooleanExpressionDecision.create(
				BoogieAstSnippet.createBooleanExpression("e", "f"));
		pattern.setScope(new srParseScopeBefore(r));
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 5 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "stinit"), r.toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st0"), r.negate().and(s.or(p.negate())).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st012"), p.and(s.negate().and(r.negate())).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st02"), r.negate().and(s.or(p.negate().and(r.negate()))).toString());
	}
	
	@Test
	public void BeforeInstAbsPatternTest(){
		//setup
		PatternType pattern = new InstAbsPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		cdd.add(s);
		pattern.mergeCDDs(cdd);	
		CDD r = BoogieBooleanExpressionDecision.create(
						BoogieAstSnippet.createBooleanExpression("c", "d"));
		pattern.setScope(new srParseScopeBefore(r));
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare basic attributes
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 5 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		//automaton specific checks
		Assert.assertTrue("Edge guard is wrong", 
				this.phaseHasTransitionLabeled(pea, "st0", r.prime().toString()));
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "stinit"), r.toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st0"), s.negate().and(r.negate()).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st012"), s.and(r.negate()).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st02"), s.negate().and(r.negate()).toString());
	}

	@Test
	public void AfterInvariantPatternTest(){
		//setup
		PatternType pattern = new InvariantPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		//this works in reverse order so result down below is right!
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("c", "d"));
		CDD p = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		cdd.add(p);
		cdd.add(s);
		pattern.mergeCDDs(cdd);	
		CDD r = BoogieBooleanExpressionDecision.create(
				BoogieAstSnippet.createBooleanExpression("e", "f"));
		pattern.setScope(new srParseScopeAfter(r));
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 3 , pea.getNumberOfLocations());
		Assert.assertEquals("Node has wrong number of edges", 2 , pea.getPhases()[0].getTransitions().size());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		Assert.assertEquals("Edge guard is wrong", "TRUE", 
				pea.getPhases()[0].getTransitions().get(0).getGuard().toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st0"),r.negate().toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st012"), r.and(s.or(p.negate())).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st02"),r.negate().and(s.or(p.negate())).toString());
	}
		
	@Test
	public void AfterInstAbsPatternTest(){
		//setup
		PatternType pattern = new InstAbsPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		cdd.add(s);
		pattern.mergeCDDs(cdd);	
		CDD r = BoogieBooleanExpressionDecision.create(
						BoogieAstSnippet.createBooleanExpression("c", "d"));
		pattern.setScope(new srParseScopeAfter(r));
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare basic attributes
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 3 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		//automaton specific checks
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st0"), r.negate().toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st012"), s.negate().and(r).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st02"), s.negate().and(r.negate()).toString());
	}
	
	@Test
	public void AfterUntilInstAbsPatternTest(){
		//setup 
		PatternType pattern = new InstAbsPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		cdd.add(s);
		pattern.mergeCDDs(cdd);	
		CDD r = BoogieBooleanExpressionDecision.create(
						BoogieAstSnippet.createBooleanExpression("c", "d"));
		CDD q = BoogieBooleanExpressionDecision.create(
				BoogieAstSnippet.createBooleanExpression("e", "f"));
		pattern.setScope(new srParseScopeAfterUntil(q, r));
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare basic attributes
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 3 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
		//automaton specific checks
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st0"), r.or(q.negate()).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st012"), s.negate().and(q).and(r.negate()).toString());
		Assert.assertEquals("Phase Guard guard is wrong", 
				this.phaseGuardedWith(pea, "st02"), s.negate().and(q.negate()).and(r.negate()).toString());
	}

	@Test
	public void BetweenInstAbsPatternTest(){
		//setup
		PatternType pattern = new InstAbsPattern();
		Vector<CDD> cdd = new Vector<CDD>();
		//this works in reverse order so result down below is right!
		CDD s = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
		cdd.add(s);
		pattern.mergeCDDs(cdd);	
		CDD r = BoogieBooleanExpressionDecision.create(
				BoogieAstSnippet.createBooleanExpression("e", "f"));
		CDD q = BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("c", "d"));
		pattern.setScope(new srParseScopeBetween(r,q));
		//test
		ArrayList<PatternType> patterns = new  ArrayList<PatternType>();
		patterns.add(pattern);
		PhaseEventAutomata pea = transformer.translate(new ArrayList<PatternType>(patterns)).get(0);
		//compare
		Assert.assertNotNull("Translatino of Pea resulted in null", pea);
		Assert.assertEquals("Automaton has wrong number of Locations", 7 , pea.getNumberOfLocations());
		Assert.assertEquals("Automaton has wrong number of Clocks", 0 , pea.getClocks().size());
	}

	
	private boolean phaseHasTransitionLabeled(PhaseEventAutomata pea, String phaseName, String label){
		for(Phase p: pea.getPhases()){
			if (p.getName().equals(phaseName)){
				for(Transition e: p.getTransitions()){
					if(e.getGuard().toString().equals(label)) return true;
				}
			}
		}
		return false;
	}
	private String phaseGuardedWith(PhaseEventAutomata pea, String phaseName){
		for(Phase p: pea.getPhases()){
			if (p.getName().equals(phaseName)){
				return p.getStateInvariant().toString();
			}
		}
		return "PHASE NOT FOUND";
	}
	
	
}

















