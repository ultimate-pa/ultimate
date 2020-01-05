package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;

public class Req2CauseTrackingPea implements IReq2Pea {
	
	private final ILogger mLogger;
	private final List<InitializationPattern> mInitPattern;
	private final List<PatternType> mPatternType;
	private final Map<PatternType, PhaseEventAutomata> mPattern2Peas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	
	public Req2CauseTrackingPea(final ILogger logger, List<InitializationPattern> init, List<PatternType> requirements) {
		mLogger = logger;
		mInitPattern = init;
		mPatternType = requirements;
		mPattern2Peas = new LinkedHashMap<>();
	}

	@Override
	public void transform(IReq2Pea req2pea) {
		final Map<PatternType, PhaseEventAutomata> simplePeas = req2pea.getPattern2Peas();
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		for (Map.Entry<PatternType, PhaseEventAutomata> entry : simplePeas.entrySet() ){
			mPattern2Peas.put(entry.getKey(), transformPea(entry.getKey(), entry.getValue(), symbolTable));
		}
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);
		for(PatternType p : mInitPattern) {
			builder.addInitPattern((InitializationPattern) p);
		}
		for (final Entry<PatternType, PhaseEventAutomata> entry : mPattern2Peas.entrySet()) {
			builder.addPea(entry.getKey(), entry.getValue());
		}
		mSymbolTable = builder.constructSymbolTable();
	}
	
	private PhaseEventAutomata transformPea(PatternType pattern, PhaseEventAutomata pea, IReqSymbolTable reqSymbolTable) {
		final Req2CauseTrackingCDD cddTransformer = new Req2CauseTrackingCDD(mLogger);
		final String name = pea.getName();
		setFlags(pea.getInit());
		final Phase[] phases = transformPhases(pattern, pea.getPhases(), cddTransformer, reqSymbolTable);
		final Phase[] init = getInitialPhases(phases);
		connectCopies(phases);
		final List<String> clocks = pea.getClocks();
		final Map<String,String> variables = pea.getVariables();
		variables.putAll(cddTransformer.getTrackingVars());
		final List<String> declarations = pea.getDeclarations();
		
		// _tt for "test tracking"
		PhaseEventAutomata ctPea = new PhaseEventAutomata(name + "_tt", phases, init, clocks, variables, declarations);
		return ctPea;
	}
	
	private void setFlags(Phase[] initialPhases) {
		for(Phase p: initialPhases) {
			p.isInit = true;
		}
	}
	
	private Phase[] transformPhases(PatternType pattern, Phase[] oldPhases, Req2CauseTrackingCDD cddTransformer, IReqSymbolTable reqSymbolTable){
		final Set<String> effectVars = cddTransformer.getEffectVariables(pattern);
		int effectPhase = getEffectPhase(oldPhases, effectVars , cddTransformer);		
		Phase[] phases = new Phase[2 * oldPhases.length];
		for (int i = 0; i < oldPhases.length; i++) {
			Phase op = oldPhases[i];
			//TODO: fit clock invariants to test tracking stuff
			phases[i] = op;
			CDD stateInvariant = cddTransformer.transform(op.getStateInvariant(), effectVars, reqSymbolTable.getInputVars(), i == effectPhase);
			Phase trackingPhase = new Phase(op.getName() + "_tt", stateInvariant, op.getClockInvariant());
			phases[oldPhases.length + i] = trackingPhase;
			if (op.isInit) trackingPhase.isInit = true;
			//add stuttering edge
			trackingPhase.addTransition(trackingPhase, CDD.TRUE, new String[0]);
		}
		return phases;
	}
	
	private int getEffectPhase(Phase[] phases, Set<String> effects, Req2CauseTrackingCDD cddTransformer) {
		//As the Peas may have some suffix after the effect, try to find the effect by finding the highest 
		//  phase where the effect is mentioned.
		//TODO: hand over the phase relevant for the effect from the automaton generation
		for(int i = phases.length-1; i >= 0; i--) {
			CDD invar = phases[i].getStateInvariant();
			if (cddTransformer.getCddVariables(invar).containsAll(effects)) return i;
		}
		return 0;
	}
	
	private Phase[] getInitialPhases(Phase[] phases) {
		List<Phase> initialPhases = new ArrayList<>();
		for(Phase p : phases) {
			if (p.isInit) initialPhases.add(p);
		}
		return initialPhases.toArray(new Phase[initialPhases.size()]);
	}

	private void connectCopies(Phase[] phases) {
		int seem = phases.length/2;
		for(int i = 0; i < seem ; i++) {
			phases[seem+i].addTransition(phases[i], CDD.TRUE, new String[0]);
			if (phases[i].isInit) {
				phases[i].addTransition(phases[seem+i], CDD.TRUE, new String[0]);
			}
		}
	}
	
	
	@Override
	public Map<PatternType, PhaseEventAutomata> getPattern2Peas() {
		return mPattern2Peas;
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		//TODO: symboltable is a nested class and can only be accessed on the builders terms, maybe change all you can in the peas and leave everything up to the pea-thing functions
		return mSymbolTable;
	}
	
	@Override
	public boolean hasErrors() {
		return mHasErrors;
	}

}
