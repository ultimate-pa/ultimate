package de.uni_freiburg.informatik.ultimate.PEATestTransformerTest.SPLPatternParser;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import pea.BoogieBooleanExpressionDecision;
import pea.BooleanDecision;
import pea.CDD;
import pea.CounterTrace;
import pea.PhaseEventAutomata;
import pea.Trace2PEACompiler;

public class CounterFormulaRegTest {
	Trace2PEACompiler compiler = new Trace2PEACompiler();
	
	CDD r,q,s,p;
	
	@Before
	public void SetUp()
	{

		r =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("e", "f"));
		q =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("c", "d"));
		s =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("x", "y"));
		p =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createBooleanExpression("a", "b"));
	}

	@Test
	public void BetweenInstAbsPatternTest()
	{
		CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    	  	    new CounterTrace.DCPhase(),
    	   	    new CounterTrace.DCPhase(q.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(s.and(r.negate())),
    	   	    new CounterTrace.DCPhase(r.negate()),
    	   	    new CounterTrace.DCPhase(r),
    	  	    new CounterTrace.DCPhase()
    	   	});    	
    	   	PhaseEventAutomata pea =  compiler.compile("TAbsBet", ct);
    	   	
    	   	Assert.assertEquals("Automaton has wrong number of Locations", 7 , pea.getNumberOfLocations());
	}
}
