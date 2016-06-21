package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser.PatternToDc;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.CounterTrace;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.PhaseSet;
import pea.Trace2PEACompiler;
import pea.CounterTrace.DCPhase;
import srParse.pattern.PatternType;

/**
 * For holing all data on the system model and for inferences of that data 
 * e.g. which phases are final.
 * @author langenfv@informatik.uni-freiburg.de
 *
 */
public class PeaSystemModel {
	
	private final SystemInformation sysInfo;
	private final ILogger logger;
	private final ArrayList<PatternType> patterns;
	private final ArrayList<CounterTrace> counterTraces;
	private final ArrayList<PhaseEventAutomata> peas;
	
	/***
	 * New system model from patterns.
	 * Does directly transform to peas.
	 * @param patterns
	 */
	public PeaSystemModel(ILogger logger, SystemInformation sysInfo, ArrayList<PatternType> patterns){
		this.sysInfo = sysInfo;
		this.logger = logger;
		this.patterns = patterns;
		
		this.logger.debug("Transforming to DCTraces");
		this.counterTraces = this.translateToDc(patterns);
		this.peas = this.translateToPea(counterTraces);
		
	}
	
	/**
	 * Determines the set of states of a pea that have the highest non
	 * counter trace state in their power set.
	 * @param pea
	 * 	pea whos final phases shall be determined
	 * @return
	 * 	set of automaton states.
	 */
	public ArrayList<Phase> getFinalPhases(PhaseEventAutomata pea){
		ArrayList<Phase> result = new ArrayList<Phase>();
		int index = this.peas.indexOf(pea);
		// peas already was altered, patterns has the right number
		CounterTrace counterTrace = counterTraces.get(index);
		DCPhase lastPhase = counterTrace.getPhases()[counterTrace.getPhases().length - 3];
		for (Phase loc : pea.getPhases()) {
			PhaseSet activePhases = loc.getPhaseBits().getPhaseSet(counterTrace.getPhases());
			for (DCPhase phase : activePhases.getPhases()) {
				if (lastPhase == phase) {
					result.add(loc);
				}

			}
		}
		return result;
	}
	
	public ArrayList<DCPhase> getDcPhases(PhaseEventAutomata pea, Phase phase){
		ArrayList<DCPhase> result = new ArrayList<DCPhase>();
		int index = this.peas.indexOf(pea);
		CounterTrace counterTrace = counterTraces.get(index);
		PhaseSet ps = phase.getPhaseBits().getPhaseSet(counterTrace.getPhases());
		return ps.getPhases();
	}
	
	private ArrayList<CounterTrace> translateToDc(ArrayList<PatternType> patterns){
		PatternToDc patternToDc = new PatternToDc();
		// Translate to Counter Traces
		ArrayList<CounterTrace> counterTraces = new ArrayList<CounterTrace>();
		for(PatternType pattern : patterns){
			CounterTrace counterTrace = patternToDc.translate(pattern);
			
			counterTraces.add(counterTrace);
		}
		return counterTraces;
	}
	
	private ArrayList<PhaseEventAutomata> translateToPea(ArrayList<CounterTrace> counterTraces){
		Trace2PEACompiler compiler = new Trace2PEACompiler();
		ArrayList<PhaseEventAutomata> peas = new ArrayList<PhaseEventAutomata>();
		for(CounterTrace ct : counterTraces){
			peas.add(compiler.compile(ct.toString(), ct));
		}
		return peas;	
	}

	public ArrayList<PatternType> getPattern(){
		return this.patterns;
	}
	public ArrayList<CounterTrace> getCounterTraces(){
		return this.counterTraces;
	}
	public ArrayList<PhaseEventAutomata> getPeas(){
		return this.peas;
	}
	public void addPea(PhaseEventAutomata pea){
		this.peas.add(pea);
	}

}
