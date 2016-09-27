package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser.PatternToDc;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.CDD;
import pea.CounterTrace;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.PhaseSet;
import pea.Trace2PEACompiler;
import pea.CounterTrace.DCPhase;
import pea.PEATestAutomaton;
import srParse.pattern.InitializationPattern;
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
	private ArrayList<PatternType> patterns = new ArrayList<PatternType>();
	private final ArrayList<CounterTrace> counterTraces;
	private final ArrayList<PhaseEventAutomata> peas;
	
	/***
	 * New system model from patterns.
	 * Directly handles the transformation to PEAs and filters out the variable definition patterns
	 * beforehand.
	 * @param patterns
	 */
	public PeaSystemModel(ILogger logger, SystemInformation sysInfo, 
			ArrayList<PatternType> unsanitizedPatterns){
		this.sysInfo = sysInfo;
		this.logger = logger;
		this.patterns = this.sanitizePatternList(unsanitizedPatterns);
		
		this.logger.debug("Transforming to DCTraces");
		//TODO: check/change types of variabels in pattern before generating PEAs 
		this.counterTraces = this.translatePatternListToDc(this.patterns);
		this.peas = this.translateToPea(counterTraces);
		
	}
	
	/*
	 * Filter out InitializationPatterns and add information on variables to system information
	 */
	private ArrayList<PatternType> sanitizePatternList(ArrayList<PatternType> unsanitizedPatterns){
		ArrayList<PatternType> aux = new ArrayList<>();
		for(PatternType pattern: unsanitizedPatterns){
			if(pattern instanceof InitializationPattern){
				InitializationPattern initPattern = ((InitializationPattern) pattern);
				switch(initPattern.getAccessability()){
					case in:
						this.sysInfo.addInputVariable(initPattern.getIdent(), initPattern.getType());
						break;
					case hidden:
						this.sysInfo.addInternalVariable(initPattern.getIdent(), initPattern.getType());
						break;
					case out:
						this.sysInfo.addOutputVariable(initPattern.getIdent(), initPattern.getType());
						break;
					default:
						new RuntimeException("Unknown Initialization pattern");
				}
			} else {
				aux.add(pattern);
			}
		}
		return aux;
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
		// peas already was altered, patterns has the right number
		CounterTrace counterTrace = this.getCounterTrace(pea);
		DCPhase lastPhase = counterTrace.getPhases()[counterTrace.getPhases().length - 3];
		DCPhase veryLastPhase = counterTrace.getPhases()[counterTrace.getPhases().length - 2];
		for (Phase loc : pea.getPhases()) {
			PhaseSet activePhases = loc.getPhaseBits().getPhaseSet(counterTrace.getPhases());
			for (DCPhase phase : activePhases.getPhases()) {
				if (lastPhase == phase || veryLastPhase == phase) {
					result.add(loc);
				}

			}
		}
		return result;
	}
	
	/***
	 * Returns true if a phase has a time constraint that is greater or equal 
	 * some time i.e. is equally undesirable for testing as finally.
	 * @param pea
	 * @param phase
	 * @return
	 */
	public boolean phaseIsUpperBoundFinal(PhaseEventAutomata pea, Phase phase){
		ArrayList<Phase> finalPhases = this.getFinalPhases(pea);
		// decide trivial cases (not final, no clock invar)
		if (phase.getClockInvariant() == CDD.TRUE) return false;
		if (!finalPhases.contains(phase)) return false;
		// is original pattern a >= pattern?
		for(DCPhase p: this.getCounterTrace(pea).getPhases()){
			if(p.getBoundType() >= CounterTrace.BOUND_GREATEREQUAL) return true;
		}
		return false;
	}
	
	/***
	 * Search for all variables that have direct data flow to the
	 * given variable.
	 * @param ident
	 * @return Set of variables with direct data flow to ident
	 */
	public HashSet<String> getConditionVariables(String ident){
		//TODO: dk
		return null;	
	}
	
	public DCPhase getFinalPhase(CounterTrace ct){
		return ct.getPhases()[ct.getPhases().length - 3];
	}
	
	public int getFinalPhaseNumber(CounterTrace ct){
		return ct.getPhases().length - 3;
	}

	/***
	 * Returns the number of the highest dcphase in an pea automatons phase
	 * @param ct
	 * @param pea
	 * @param automatonPhase
	 * @return
	 */
	public int getDCPhasesMax(CounterTrace ct, PhaseEventAutomata pea, Phase automatonPhase){
		ArrayList<DCPhase> statePhases = this.getDcPhases(pea, automatonPhase);
		int highest = -1;
		DCPhase[] tracePhases = ct.getPhases();
		for(DCPhase phase: statePhases){
			for(int i = 0; i < tracePhases.length; i++){
				if(tracePhases[i] == phase && highest < i){
					highest = i;
				}
			}
		}
		return highest;
	}
	
	public ArrayList<DCPhase> getDcPhases(PhaseEventAutomata pea, Phase phase){
		ArrayList<DCPhase> result = new ArrayList<DCPhase>();
		CounterTrace counterTrace = this.getCounterTrace(pea);
		PhaseSet ps = phase.getPhaseBits().getPhaseSet(counterTrace.getPhases());
		return ps.getPhases();
	}
	
	private ArrayList<CounterTrace> translatePatternListToDc(ArrayList<PatternType> patterns){
		PatternToDc patternToDc = new PatternToDc();
		// Translate to Counter Traces
		ArrayList<CounterTrace> counterTraces = new ArrayList<CounterTrace>();
		for(PatternType pattern : patterns){
			// make PEA from remaining patterns
			CounterTrace counterTrace = patternToDc.translate(pattern); 
			counterTraces.add(counterTrace);
		}
		return counterTraces;
	}
	
	private ArrayList<PhaseEventAutomata> translateToPea(ArrayList<CounterTrace> counterTraces){
		Trace2PEACompiler compiler = new Trace2PEACompiler(this.logger);
		ArrayList<PhaseEventAutomata> peas = new ArrayList<PhaseEventAutomata>();
		for(CounterTrace ct : counterTraces){
			peas.add(compiler.compile(ct.toString(), ct));
		}
		return peas;	
	}
	
	public CDD getViolatingPhaseInvariant(PhaseEventAutomata pea){
		return null;
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
	public SystemInformation getSystemInformation(){
		return this.sysInfo;
	}
	public PatternType getPattern(PhaseEventAutomata pea) {
		int index = this.peas.indexOf(pea);
		return this.patterns.get(index);
	}
	public PatternType getPattern(int reqNo) {
		return this.patterns.get(reqNo);
	}
	public CounterTrace getCounterTrace(PhaseEventAutomata pea){
		int index = this.peas.indexOf(pea);
		return this.counterTraces.get(index);
	}
	/**
	 * returns the ith phase of the DC formula of a pea.
	 * @param pea
	 * 	the pea the according DC formula is searched
	 * @param i
	 * 	the number of the phase (negative numbers start at the end of the DC formula)
	 * @return
	 *  the ith phase or the len(phases)-i th phase
	 */
	public DCPhase getCounterTracePhase(PhaseEventAutomata pea, int i){
		DCPhase[] phases = this.getCounterTrace(pea).getPhases();
		if(i < 0){
			i = phases.length + i;
		}
		return phases[i];
	}



}
