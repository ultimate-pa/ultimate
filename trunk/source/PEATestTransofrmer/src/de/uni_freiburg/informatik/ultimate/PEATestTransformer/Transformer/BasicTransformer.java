package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import pea.CDD;
import pea.CounterTrace;
import pea.PhaseEventAutomata;
import pea.Trace2PEACompiler;
import srParse.srParseScopeAfter;
import srParse.srParseScopeAfterUntil;
import srParse.srParseScopeBefore;
import srParse.srParseScopeBetween;
import srParse.srParseScopeGlob;
import srParse.pattern.BndResponsePattern;
import srParse.pattern.InstAbsPattern;
import srParse.pattern.InvariantPattern;
import srParse.pattern.PatternType;
import srParse.pattern.UniversalityPattern;

/***
 * Easily modifiable requirements pattern to Pea transformation.
 * 
 * @author Langenfeld
 * 
 * TODO: complete rewrite of pattern! 
 *
 */
public class BasicTransformer {
	Trace2PEACompiler compiler = new Trace2PEACompiler();
	PatternToDc patternToDc = new PatternToDc();
	
	protected int reqNumber = 0;
	protected int reqMaxNumber;
	/**
	 * Translates a pattern into a Phase Event Automaton
	 * @param pattern spl pattern
	 * @return automaton of pattern
	 */
	public final List<PhaseEventAutomata> translate(ArrayList<PatternType> patterns){
		ArrayList<PhaseEventAutomata> peas = new ArrayList<PhaseEventAutomata>();
		ArrayList<CounterTrace> counterTraces = new ArrayList<CounterTrace>();
		this.preProcess(patterns);
		this.reqMaxNumber = patterns.size()-1;
		for(PatternType pattern : patterns)
		{
			CounterTrace counterTrace = this.translateToDc(pattern);
			counterTraces.add(counterTrace);
			peas.add(this.compiler.compile(pattern.toString(), counterTrace));
			reqNumber++;
		}
		return postProcess(patterns, counterTraces, peas);
	}
	
	/*
	 * This Method can be extended to analyze the input automata before the translation 
	 * is begun e.g. to collect all vairables.
	 */
	protected void preProcess(ArrayList<PatternType> patterns){
	}
	
	/*
	 * This Method can be extended to postprocess the output, 
	 * e.g. to add automata for special purposes
	 */
	protected ArrayList<PhaseEventAutomata> postProcess(ArrayList<PatternType> pats, ArrayList<CounterTrace> counterTraces, 
			ArrayList<PhaseEventAutomata> peas) {	
		return peas; 
	}


	private CounterTrace translateToDc(PatternType pattern){
		//get CDDs
		 
		CDD q = pattern.getScope().getCdd1(); 
		CDD r = pattern.getScope().getCdd2();
		CDD s = null;
		CDD p = null;
		if (pattern.getCdds().size() > 1)
			{
				s =  pattern.getCdds().get(0);
				p = pattern.getCdds().get(1);
			} else {
				p = pattern.getCdds().get(0);
			}
		int t = pattern.getDuration();
		return this.patternToDc.translate(pattern, p, q, r, s, t);
	} 

}
