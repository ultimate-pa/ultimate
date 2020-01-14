package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;

public class Req2CauseTrackingPea implements IReq2Pea {

	private final ILogger mLogger;
	private final List<InitializationPattern> mInitPattern;
	private final Map<PatternType, PhaseEventAutomata> mPattern2Peas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Map<PhaseEventAutomata, Set<Integer>> mPea2EffectPhase;
	private final Map<PhaseEventAutomata, Set<Integer>> mOutputEffectPhase;
	private final Map<PhaseEventAutomata, Set<String>> mPea2EffectVars;
	final Req2CauseTrackingCDD mCddTransformer;

	public Req2CauseTrackingPea(final IUltimateServiceProvider services, final ILogger logger,
			List<InitializationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mPattern2Peas = new LinkedHashMap<>();
		mPea2EffectPhase = new HashMap<>();
		mOutputEffectPhase = new HashMap<>();
		mPea2EffectVars = new HashMap<>();
		mCddTransformer = new Req2CauseTrackingCDD(mLogger);
	}

	@Override
	public void transform(IReq2Pea req2pea) {
		final Map<PatternType, PhaseEventAutomata> simplePeas = req2pea.getPattern2Peas();
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		for (final Map.Entry<PatternType, PhaseEventAutomata> entry : simplePeas.entrySet() ){
			mPattern2Peas.put(entry.getKey(), transformPea(entry.getKey(), entry.getValue(), symbolTable));
		}
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);
		for(final PatternType p : mInitPattern) {
			builder.addInitPattern((InitializationPattern) p);
		}
		for (final Entry<PatternType, PhaseEventAutomata> entry : mPattern2Peas.entrySet()) {
			builder.addPea(entry.getKey(), entry.getValue());
		}
		mSymbolTable = builder.constructSymbolTable();
	}

	private PhaseEventAutomata transformPea(final PatternType pattern, final PhaseEventAutomata oldPea, final IReqSymbolTable reqSymbolTable) {
		final Set<String> effectVars = mCddTransformer.getEffectVariables(pattern);
		// _tt for "test tracking"
		final String newName = oldPea.getName() + "_tt";
		setFlags(oldPea.getInit());
		final Phase[] oldPhases = oldPea.getPhases();
		final int dcEffectPhase = getDCEffectPhaseIndex(oldPhases);
		final Phase[] newPhases = transformPhases(pattern, oldPea, reqSymbolTable, effectVars, dcEffectPhase);
		final Phase[] newInit = getInitialPhases(oldPhases);
		copyOldTransitions(oldPea.getPhases(), newPhases, effectVars);
		connectTrackingAutomaton(newPhases, oldPhases, effectVars, reqSymbolTable, new ArrayList<String>(oldPea.getClocks()));
		final List<String> newClocks = new ArrayList<>(oldPea.getClocks());
		final Map<String,String> newVariables = new HashMap<>(oldPea.getVariables());
		newVariables.putAll(mCddTransformer.getTrackingVars());
		//final List<String> declarations = new ArrayList<String>(oldPea.getDeclarations());

		final PhaseEventAutomata newPea = new PhaseEventAutomata(newName, newPhases, newInit, newClocks, newVariables, null);
		// remember effect phases and output effect phases
		mPea2EffectVars.put(newPea, effectVars);
		getOutputEffectPhases(oldPea, newPea, effectVars, reqSymbolTable, dcEffectPhase);

		return newPea;
	}

	private void getOutputEffectPhases(final PhaseEventAutomata oldPea, final PhaseEventAutomata newPea,
			final Set<String> effectVars, final IReqSymbolTable reqSymbolTable, final int effectPhase) {
		mPea2EffectPhase.put(newPea, new HashSet<Integer>());
		mOutputEffectPhase.put(newPea, new HashSet<Integer>());
		final Phase[] oldPhases = oldPea.getPhases();
		for (int i = 0; i < oldPhases.length; i++) {
			if (oldPhases[i].getPhaseBits().isActive(effectPhase) && !oldPhases[i].getPhaseBits().isWaiting(effectPhase)) {
				final int newEffectPhase = oldPea.getPhases().length + i;
				mPea2EffectPhase.get(newPea).add(newEffectPhase);
				if (!Collections.disjoint(effectVars, reqSymbolTable.getOutputVars())) {
					mOutputEffectPhase.get(newPea).add(newEffectPhase);
				}
			}
			//TODO do same thing but for outgoing edges
		}
	}

	private void setFlags(Phase[] initialPhases) {
		for(final Phase p: initialPhases) {
			p.isInit = true;
		}
	}

	private Phase[] transformPhases(PatternType pattern, PhaseEventAutomata oldPea, IReqSymbolTable reqSymbolTable, final Set<String> effectVars, final int effectPhase){
		final Phase[] oldPhases = oldPea.getPhases();
		final Phase[] newPhases = new Phase[2 * oldPhases.length];
		for (int i = 0; i < oldPhases.length; i++) {
			final Phase oldPhase = oldPhases[i];
			//TODO: fit clock invariants to test tracking stuff
			newPhases[i] = new Phase(oldPhase.getName(), oldPhase.getStateInvariant(), oldPhase.getClockInvariant());
			final CDD stateInvariant = mCddTransformer.transformInvariant(oldPhase.getStateInvariant(), effectVars,
					reqSymbolTable.getInputVars(), oldPhase.getPhaseBits().isActive(effectPhase) && !oldPhase.getPhaseBits().isWaiting(effectPhase));
			final Phase trackingPhase = new Phase(oldPhase.getName() + "_tt", stateInvariant, oldPhase.getClockInvariant());
			newPhases[oldPhases.length + i] = trackingPhase;
			if (oldPhase.isInit) {
				trackingPhase.isInit = true;
			}
		}
		return newPhases;
	}

	private int getDCEffectPhaseIndex(Phase[] oldPhases) {
		//Find the last phase that is 1) active and 2) not waiting (to get active)
		int lastDcPhase = 0;
		for(int i = 0; i < oldPhases.length; i++) {
			for(final Phase p: oldPhases) {
				if (p.getPhaseBits().isActive(i) && !p.getPhaseBits().isWaiting(i) && i > lastDcPhase) {
					lastDcPhase = i;
				}
			}
		}
		return lastDcPhase;
	}

	private Phase[] getInitialPhases(Phase[] phases) {
		final List<Phase> initialPhases = new ArrayList<>();
		for(final Phase p : phases) {
			if (p.isInit) {
				initialPhases.add(p);
			}
		}
		return initialPhases.toArray(new Phase[initialPhases.size()]);
	}

	private void copyOldTransitions(Phase[] oldPhases, Phase[] newPhases, Set<String> effectVars) {
		final List<Phase> indexList = Arrays.asList(oldPhases);
		for(int i = 0; i < oldPhases.length ; i++) {
			for(final Transition trans : oldPhases[i].getTransitions()) {
				final int dest = indexList.indexOf(trans.getDest());
				newPhases[i].addTransition(newPhases[dest], trans.getGuard(), trans.getResets());

			}
		}
	}

	private void connectTrackingAutomaton(Phase[] newPhases, Phase[] oldPhases, final Set<String> effectVars, final IReqSymbolTable reqSymbolTable, List<String> clocks) {
		final int seem = newPhases.length/2;
		final List<Phase> indexList = Arrays.asList(newPhases);
		//copy edges in first to second automaton
		for(int i = 0; i < seem ; i++) {
			for(final Transition trans : newPhases[i].getTransitions()) {
				final int dest = indexList.indexOf(trans.getDest());
				final Phase sourcePhase = newPhases[seem + i];
				//apply same transformations to CDDs must be done as in the invariants
				final CDD guard = mCddTransformer.transformGurad(trans.getGuard(), effectVars, reqSymbolTable.getInputVars(), false);
				sourcePhase.addTransition(newPhases[seem + dest], guard, trans.getResets());
			}
		}
		//conect the copies
		for(int i = 0; i < seem ; i++) {
			newPhases[seem + i].addTransition(newPhases[i], CDD.TRUE, new String[0]);
			if (oldPhases[i].isInit) {
				newPhases[i].addTransition(newPhases[seem + i], CDD.TRUE, clocks.toArray(new String[clocks.size()]));
			}
		}
	}

	public Map<PhaseEventAutomata, Set<Integer>> getEffectPhase(){
		return mPea2EffectPhase;
	}

	public Map<PhaseEventAutomata, Set<Integer>> getOutputEffectPhase(){
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
