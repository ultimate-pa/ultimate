package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.CDD;
import pea.CounterTrace;
import pea.CounterTrace.DCPhase;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.PhaseSet;
import pea.Trace2PEACompiler;
import pea.Transition;
import srParse.pattern.PatternType;

public class DeductionGuardTransromation extends BasicTransformer {
	private SystemInformation sysInfo;
	private ILogger logger;
	private final static String CLOSED_WORLD_PREFIX = "R_";
	private final static String CLOSED_WORLD_SEPR = "_";
	private final static String READ_GUARD_PREFIX = "L_"; 
	
	public DeductionGuardTransromation(ILogger logger, SystemInformation sysInfo){
		this.sysInfo = sysInfo;
		this.logger = logger;
	}
	
	/**
	 * 
	 */
	@Override
	protected ArrayList<PhaseEventAutomata> postProcess(ArrayList<PatternType> pats, ArrayList<CounterTrace> counterTraces, 
			ArrayList<PhaseEventAutomata> peas) {
		// add deduction guard to every edge of the automaton
		for(int i = 0; i < pats.size(); i++){
			PhaseEventAutomata pea = peas.get(i);
			CounterTrace counterTrace = counterTraces.get(i);
			// get last active phase of counter trace automaton
			//int lastphase = counterTrace.getPhases().length -3;
			DCPhase lastPhase = counterTrace.getPhases()[counterTrace.getPhases().length-3];
			for(Phase loc: pea.getPhases()){
				for(Transition trans: loc.getTransitions()){
					boolean destinationHasLastPhase = false;
					//build conjunct from phase invariants (invariant - seeps)
					DCPhase[] phases = null;
					PhaseSet activePhases = trans.getDest().getPhaseBits().getPhaseSet(phases);
					CDD invariant = CDD.TRUE;
					for(DCPhase phase: activePhases.getPhases()){
						invariant = invariant.and(phase.getInvariant());
						if(lastPhase == phase){
							destinationHasLastPhase = true;
						}
					}
					trans.setGuard(
							trans.getGuard().and(
							this.dmGuard(counterTrace, invariant, destinationHasLastPhase, false))
							);
				}
			}
		}
		//TODO: add deduction guard automata
		return peas;
	}
	
	private CDD dmGuard(CounterTrace ct, CDD invariant, boolean hasLastPhase, boolean disjunction){
		logger.info(ct.toString());
		return CDD.TRUE;
	}
	
}
