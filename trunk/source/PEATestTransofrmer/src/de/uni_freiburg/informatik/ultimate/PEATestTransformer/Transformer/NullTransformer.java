package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PeaSystemModel;
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
 */
public class NullTransformer implements IPeaTransformer {
	
	/**
	 * Translates a pattern into a Phase Event Automaton
	 * @param pattern spl pattern
	 * @return automaton of pattern
	 */
	@Override
	public void translate() {	
	}




}
