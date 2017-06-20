package de.uni_freiburg.informatik.ultimate.PEATestTransformerTest.SPLPatternParser;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser.PatternToDc;
import pea.BoogieBooleanExpressionDecision;
import pea.BooleanDecision;
import pea.CDD;
import pea.CounterTrace;
import pea.PhaseEventAutomata;
import pea.Trace2PEACompiler;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;

public class CounterFormulaRegTest {
	Trace2PEACompiler compiler = new Trace2PEACompiler();
	PatternToDc patternToDc = new PatternToDc();
	
	CDD r,q,s,p;
	
	@Before
	public void SetUp(){

		r =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createIdentifier("r"));
		q =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createIdentifier("q"));
		s =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createIdentifier("s"));
		p =  BoogieBooleanExpressionDecision
				.create(BoogieAstSnippet.createIdentifier("p"));
	}

	@Test
	public void GlobalInvariantTest(){
		//TODO: testing here
	}
}
