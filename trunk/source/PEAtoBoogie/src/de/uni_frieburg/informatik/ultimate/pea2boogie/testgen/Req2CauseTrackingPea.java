package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.ReqCheckAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;

public class Req2CauseTrackingPea implements IReq2Pea {
	
	private final ILogger mLogger;
	private final List<InitializationPattern> mInitPattern;
	private final Map<PatternType, PhaseEventAutomata> mPattern2Peas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private Map<PhaseEventAutomata, Integer> mPea2EffectPhase;
	private Map<PhaseEventAutomata, Integer> mOutputEffectPhase;
	private Map<PhaseEventAutomata, Set<String>> mPea2EffectVars;
	
	public Req2CauseTrackingPea(final IUltimateServiceProvider services, final ILogger logger,
			List<InitializationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mPattern2Peas = new LinkedHashMap<>();
		mPea2EffectPhase = new HashMap<>();
		mOutputEffectPhase = new HashMap<>();
		mPea2EffectVars = new HashMap<>();
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
	
	private PhaseEventAutomata transformPea(final PatternType pattern, final PhaseEventAutomata oldPea, final IReqSymbolTable reqSymbolTable) {
		
		final Req2CauseTrackingCDD cddTransformer = new Req2CauseTrackingCDD(mLogger);
		final String newName = oldPea.getName() + "_tt";
		setFlags(oldPea.getInit());
		final Phase[] newPhases = transformPhases(pattern, oldPea, cddTransformer, reqSymbolTable);
		final Phase[] newInit = getInitialPhases(newPhases);
		copyTransitions(oldPea.getPhases(), newPhases);
		connectCopies(newPhases);
		final List<String> newClocks = new ArrayList<>(oldPea.getClocks());
		final Map<String,String> newVariables = new HashMap<>(oldPea.getVariables());
		newVariables.putAll(cddTransformer.getTrackingVars());
		//final List<String> declarations = new ArrayList<String>(oldPea.getDeclarations());
		
		// _tt for "test tracking"
		PhaseEventAutomata newPea = new PhaseEventAutomata(newName, newPhases, newInit, newClocks, newVariables, null);
		
		// remember effect phases and output effect phases
		Set<String> effectVars = cddTransformer.getEffectVariables(pattern);
		mPea2EffectVars.put(newPea, effectVars);
		int effectPhase = getEffectPhase(oldPea.getPhases(), effectVars , cddTransformer);	
		int newEffectPhase = oldPea.getPhases().length + effectPhase;
		mPea2EffectPhase.put(newPea, newEffectPhase);
		if (!Collections.disjoint(effectVars, reqSymbolTable.getOutputVars())) {
			mOutputEffectPhase.put(newPea, newEffectPhase);
		}
		return newPea;
	}
	
	private void setFlags(Phase[] initialPhases) {
		for(Phase p: initialPhases) {
			p.isInit = true;
		}
	}
	
	private Phase[] transformPhases(PatternType pattern, PhaseEventAutomata pea, Req2CauseTrackingCDD cddTransformer, IReqSymbolTable reqSymbolTable){
		final Set<String> effectVars = cddTransformer.getEffectVariables(pattern);
		Phase[] oldPhases = pea.getPhases();
		int effectPhase = getEffectPhase(oldPhases, effectVars , cddTransformer);	
		Phase[] phases = new Phase[2 * oldPhases.length];
		for (int i = 0; i < oldPhases.length; i++) {
			Phase op = oldPhases[i];
			//TODO: fit clock invariants to test tracking stuff
			phases[i] = new Phase(op.getName() + "_tt", op.getClockInvariant(), op.getClockInvariant());
			CDD stateInvariant = cddTransformer.transform(op.getStateInvariant(), effectVars, reqSymbolTable.getInputVars(), i == effectPhase);
			Phase trackingPhase = new Phase(op.getName() + "_tt", stateInvariant, op.getClockInvariant());
			phases[oldPhases.length + i] = trackingPhase;
			if (op.isInit) {
				trackingPhase.isInit = true;
			}
		}
		return phases;
	}
	
	private int getEffectPhase(Phase[] phases, Set<String> effects, Req2CauseTrackingCDD cddTransformer) {
		//As the Peas may have some suffix after the effect, try to find the effect by finding the highest 
		//  phase where the effect is mentioned.
		//TODO: hand over the phase relevant for the effect from the automaton generation
		for(int i = phases.length-1; i >= 0; i--) {
			CDD invar = phases[i].getStateInvariant();
			if (cddTransformer.getCddVariables(invar).containsAll(effects)) {
				return i;
			}
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
	
	private void copyTransitions(Phase[] oldPhases, Phase[] newPhases) {
		List<Phase> indexList = Arrays.asList(oldPhases);
		for(int i = 0; i < oldPhases.length ; i++) {
			for(Transition trans : oldPhases[i].getTransitions()) {
				int index = indexList.indexOf(trans.getDest());
				newPhases[i].addTransition(newPhases[index], trans.getGuard(), trans.getResets());
			}
		}
	}

	private void connectCopies(Phase[] phases) {
		int seem = phases.length/2;
		List<Phase> indexList = Arrays.asList(phases);
		//copy edges in first to second automaton
		for(int i = 0; i < seem ; i++) {
			for(Transition trans : phases[i].getTransitions()) {
				int index = seem +  indexList.indexOf(trans.getDest());
				phases[seem + i].addTransition(phases[index], trans.getGuard(), trans.getResets());
			}
		}
		//conect the copies
		for(int i = 0; i < seem ; i++) {
			phases[seem+i].addTransition(phases[i], CDD.TRUE, new String[0]);
			if (phases[i].isInit) {
				phases[i].addTransition(phases[seem+i], CDD.TRUE, new String[0]);
			}
		}
	}
	
	public Map<PhaseEventAutomata, Integer> getEffectPhase(){
		return mPea2EffectPhase;
	}
	
	public Map<PhaseEventAutomata, Integer> getOutputEffectPhase(){
		return mOutputEffectPhase;
	}
	
	public Map<PhaseEventAutomata, Set<String>> getPea2EffectVars(){
		return mPea2EffectVars;
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

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		return new ReqTestAnnotator(mServices, mLogger, this);
	}

}
