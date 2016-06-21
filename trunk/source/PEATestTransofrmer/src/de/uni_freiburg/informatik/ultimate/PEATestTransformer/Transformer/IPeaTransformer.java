package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;

import pea.CounterTrace;
import pea.PhaseEventAutomata;
import srParse.pattern.PatternType;

public interface IPeaTransformer {
	
	public ArrayList<PhaseEventAutomata> translate(ArrayList<PatternType> pats,
			ArrayList<CounterTrace> counterTraces, ArrayList<PhaseEventAutomata> peas);
	

}
