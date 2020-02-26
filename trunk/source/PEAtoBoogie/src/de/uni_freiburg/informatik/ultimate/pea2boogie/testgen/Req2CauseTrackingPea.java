package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

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
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;

public class Req2CauseTrackingPea implements IReq2Pea {

	private final ILogger mLogger;
	private final List<InitializationPattern> mInitPattern;
	private final Map<PatternType, PhaseEventAutomata> mPattern2Peas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Map<PhaseEventAutomata, ReqEffectStore> mPea2EffectStore;
	final Req2CauseTrackingCDD mCddTransformer;

	public Req2CauseTrackingPea(final IUltimateServiceProvider services, final ILogger logger,
			final List<InitializationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mPea2EffectStore = new HashMap<>();
		mPattern2Peas = new LinkedHashMap<>();
		mCddTransformer = new Req2CauseTrackingCDD(mLogger);
	}

	@Override
	public void transform(final IReq2Pea req2pea) {
		final Map<PatternType, PhaseEventAutomata> simplePeas = req2pea.getPattern2Peas();
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);
		for (final PatternType p : mInitPattern) {
			builder.addInitPattern((InitializationPattern) p);
		}
		for (final Map.Entry<PatternType, PhaseEventAutomata> entry : simplePeas.entrySet()) {
			mPattern2Peas.put(entry.getKey(), transformPea(entry.getKey(), entry.getValue(), symbolTable));
		}
		for (final Entry<PatternType, PhaseEventAutomata> entry : mPattern2Peas.entrySet()) {
			builder.addPea(entry.getKey(), entry.getValue());
		}
		mSymbolTable = builder.constructSymbolTable();
	}

	private PhaseEventAutomata transformPea(final PatternType pattern, final PhaseEventAutomata oldPea,
			final IReqSymbolTable reqSymbolTable) {
		final ReqEffectStore reqEffectStore = new ReqEffectStore();

		final CDD effectCdd = Req2CauseTrackingCDD.getEffectCDD(pattern);
		final Set<String> effectVars = Req2CauseTrackingCDD.getCddVariables(effectCdd);
		mLogger.info(new StringBuilder("Effect Variables of ").append(pattern.toString()).append(": ")
				.append(effectVars.toString()).toString());
		// _tt for "test tracking"
		final String newName = oldPea.getName() + "_tt";
		setFlags(oldPea.getInit());
		final Phase[] oldPhases = oldPea.getPhases();
		final int dcEffectPhase = getDCEffectPhaseIndex(oldPhases, effectCdd);
		final Phase[] newPhases =
				transformPhases(pattern, oldPea, reqSymbolTable, effectCdd, effectVars, dcEffectPhase);
		final Phase[] newInit = getInitialPhases(oldPhases);
		copyOldTransitions(oldPea.getPhases(), newPhases, effectVars);
		connectTrackingAutomaton(newPhases, oldPhases, effectVars, reqSymbolTable, new ArrayList<>(oldPea.getClocks()));
		final List<String> newClocks = new ArrayList<>(oldPea.getClocks());
		final Map<String, String> newVariables = new HashMap<>(oldPea.getVariables());
		newVariables.putAll(mCddTransformer.getTrackingVars());
		// final List<String> declarations = new ArrayList<String>(oldPea.getDeclarations());

		final PhaseEventAutomata newPea =
				new PhaseEventAutomata(newName, newPhases, newInit, newClocks, newVariables, null);
		mPea2EffectStore.put(newPea, reqEffectStore);
		// remember effect phases and output effect phases
		reqEffectStore.addEffectVars(effectVars);
		getOutputEffectPhases(oldPea, reqEffectStore, effectVars, reqSymbolTable, dcEffectPhase, effectCdd);
		return newPea;
	}

	private static void getOutputEffectPhases(final PhaseEventAutomata oldPea, final ReqEffectStore reqEffectStore,
			final Set<String> effectVars, final IReqSymbolTable reqSymbolTable, final int dcEffectPhase,
			final CDD effectCdd) {
		final Phase[] oldPhases = oldPea.getPhases();
		final List<Phase> phaseList = Arrays.asList(oldPhases);
		for (int i = 0; i < oldPhases.length; i++) {
			final int offset = oldPea.getPhases().length;
			// decide which pea phases have an effect
			final int newEffectPhaseIndex = offset + i;
			if (phaseIsEffectPhase(oldPhases[i], dcEffectPhase, effectCdd)) {
				reqEffectStore.addEffectPhaseIndex(newEffectPhaseIndex);
				if (!Collections.disjoint(effectVars, reqSymbolTable.getOutputVars())) {
					reqEffectStore.addOutputEffectPhaseIndex(newEffectPhaseIndex);
				}
			}
			// decide which pea transitions have an effect
			for (final Transition t : oldPhases[i].getTransitions()) {
				if (isEffectTransition(t.getSrc(), t, dcEffectPhase, effectCdd)) {
					final Integer newTargetPhaseIndex = offset + phaseList.indexOf(t.getDest());
					reqEffectStore.addEffectEdgeIndex(newEffectPhaseIndex, newTargetPhaseIndex);
					if (!Collections.disjoint(effectVars, reqSymbolTable.getOutputVars())) {
						reqEffectStore.addOutputEffectEdgeIndex(newEffectPhaseIndex, newTargetPhaseIndex);
					}
				}
			}
		}
	}

	private static boolean phaseIsEffectPhase(final Phase phase, final int effectDCPhase, final CDD effectCdd) {
		return phase.getPhaseBits() != null && phase.getPhaseBits().isActive(effectDCPhase)
				&& !phase.getPhaseBits().isWaiting(effectDCPhase)
				&& phase.getStateInvariant().and(effectCdd.negate()) == CDD.FALSE;
	}

	private static boolean isEffectTransition(final Phase source, final Transition transition, final int effectDCPhase,
			final CDD effectCdd) {
		return source.getPhaseBits() != null && source.getPhaseBits().isActive(effectDCPhase)
				&& transition.getGuard().and(effectCdd.negate().prime(Collections.emptySet())) == CDD.FALSE;
	}

	private static void setFlags(final Phase[] initialPhases) {
		for (final Phase p : initialPhases) {
			p.isInit = true;
		}
	}

	private Phase[] transformPhases(final PatternType pattern, final PhaseEventAutomata oldPea,
			final IReqSymbolTable reqSymbolTable, final CDD effectCdd, final Set<String> effectVars,
			final int effectPhase) {
		final Phase[] oldPhases = oldPea.getPhases();
		final Phase[] newPhases = new Phase[2 * oldPhases.length];
		for (int i = 0; i < oldPhases.length; i++) {
			final Phase oldPhase = oldPhases[i];
			// TODO: fit clock invariants to test tracking stuff
			newPhases[i] = new Phase(oldPhase.getName(), oldPhase.getStateInvariant(), oldPhase.getClockInvariant());
			final CDD stateInvariant = mCddTransformer.transformInvariant(oldPhase.getStateInvariant(), effectVars,
					reqSymbolTable.getInputVars(), phaseIsEffectPhase(oldPhase, effectPhase, effectCdd));
			final Phase trackingPhase =
					new Phase(oldPhase.getName() + "_tt", stateInvariant, oldPhase.getClockInvariant());
			newPhases[oldPhases.length + i] = trackingPhase;
			if (oldPhase.isInit) {
				trackingPhase.isInit = true;
			}
		}
		return newPhases;
	}

	private static int getDCEffectPhaseIndex(final Phase[] oldPhases, final CDD effectCdd) {
		// Find the last phase that is 1) active and 2) not waiting (to get active)
		int lastDcPhase = 0;
		for (int i = 0; i < oldPhases.length; i++) {
			for (final Phase p : oldPhases) {
				if (phaseIsEffectPhase(p, i, effectCdd) && i > lastDcPhase) {
					lastDcPhase = i;
				}
			}
		}
		return lastDcPhase;
	}

	private static Phase[] getInitialPhases(final Phase[] phases) {
		final List<Phase> initialPhases = new ArrayList<>();
		for (final Phase p : phases) {
			if (p.isInit) {
				initialPhases.add(p);
			}
		}
		return initialPhases.toArray(new Phase[initialPhases.size()]);
	}

	private static void copyOldTransitions(final Phase[] oldPhases, final Phase[] newPhases,
			final Set<String> effectVars) {
		final List<Phase> indexList = Arrays.asList(oldPhases);
		for (int i = 0; i < oldPhases.length; i++) {
			for (final Transition trans : oldPhases[i].getTransitions()) {
				final int dest = indexList.indexOf(trans.getDest());
				newPhases[i].addTransition(newPhases[dest], trans.getGuard(), trans.getResets());
			}
		}
	}

	private void connectTrackingAutomaton(final Phase[] newPhases, final Phase[] oldPhases,
			final Set<String> effectVars, final IReqSymbolTable reqSymbolTable, final List<String> clocks) {
		final int seem = newPhases.length / 2;
		final List<Phase> indexList = Arrays.asList(newPhases);
		// copy edges in first to second automaton
		for (int i = 0; i < seem; i++) {
			for (final Transition trans : newPhases[i].getTransitions()) {
				final int dest = indexList.indexOf(trans.getDest());
				final Phase sourcePhase = newPhases[seem + i];
				// apply same transformations to CDDs must be done as in the invariants
				final CDD guard = mCddTransformer.transformGurad(trans.getGuard(), effectVars,
						reqSymbolTable.getInputVars(), false);
				sourcePhase.addTransition(newPhases[seem + dest], guard, trans.getResets());
			}
		}
		// conect the copies
		for (int i = 0; i < seem; i++) {
			newPhases[seem + i].addTransition(newPhases[i], CDD.TRUE, new String[0]);
			if (oldPhases[i].isInit) {
				newPhases[i].addTransition(newPhases[seem + i], CDD.TRUE, clocks.toArray(new String[clocks.size()]));
			}
		}
	}

	public Map<PhaseEventAutomata, ReqEffectStore> getReqEffectStore() {
		return mPea2EffectStore;
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
