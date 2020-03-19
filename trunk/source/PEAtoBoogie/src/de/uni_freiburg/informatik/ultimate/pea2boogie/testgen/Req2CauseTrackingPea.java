package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

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

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
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
	final BoogieLocation mLocation = new BoogieLocation("", -1, -1, -1, -1);

	final static String LOWER_AUTOMATON_SUFFIX = "_tt";

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
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);
		for (final PatternType p : mInitPattern) {
			builder.addInitPattern((InitializationPattern) p);
			if (((InitializationPattern) p).getCategory() == VariableCategory.OUT) {
				builder.addAuxvar(mLocation ,
						ReqTestAnnotator.getTrackingVar(p.getId()), "bool");
			}
		}
		final Map<PatternType, PhaseEventAutomata> simplePeas = req2pea.getPattern2Peas();
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		for (final Map.Entry<PatternType, PhaseEventAutomata> entry : simplePeas.entrySet()) {
			mPattern2Peas.put(entry.getKey(), transformPea(entry.getKey(), entry.getValue(), symbolTable, builder.getId2Bounds()));
		}
		for (final Entry<PatternType, PhaseEventAutomata> entry : mPattern2Peas.entrySet()) {
			builder.addPea(entry.getKey(), entry.getValue());
		}
		builder.addAuxvar(mLocation, ReqTestAnnotator.INITIAL_STEP_FLAG , "bool");
		mSymbolTable = builder.constructSymbolTable();
	}

	/*
	 * Make two copies of the peas that are connected by Transitions from each state to its copy.
	 * The upper automaton (lower half of the array of Locations) prevents bad things from happening i.e. only accepts
	 * runs that do not violate the requirement. The lower automaton (upper half of the array) keeps information
	 * over the determindness of all variables.
	 */
	private PhaseEventAutomata transformPea(final PatternType pattern, final PhaseEventAutomata oldPea,
			final IReqSymbolTable reqSymbolTable, Map<String, Integer> id2Bounds) {

		final ReqEffectStore reqEffectStore = new ReqEffectStore();
		final DCPhase[] dcFormula = pattern.constructCounterTrace(id2Bounds).getPhases();
		//TODO: get Effect CDD still relies on the  pattern, change to DC formula (must change getVariables too)
		final CDD effectCdd = Req2CauseTrackingCDD.getEffectCDD(pattern);
		final Set<String> effectVars = Req2CauseTrackingCDD.getCddVariables(effectCdd);
		//TODO: final Set<String> effectVars = mCddTransformer.getEffectVariables(pattern, id2bounds);
		mLogger.info(new StringBuilder("Effect Variables of ").append(pattern.toString()).append(": ")
				.append(effectVars.toString()).toString());
		setFlags(oldPea.getInit());
		final Phase[] oldLocations = oldPea.getPhases();
		final int dcEffectPhase = getDCEffectPhaseIndex(oldLocations, effectCdd);
		final Phase[] newLocations =
				transformLocations(pattern, oldPea, reqSymbolTable, effectCdd, effectVars, dcEffectPhase, dcFormula);
		final Phase[] newInit = getInitialPhases(oldLocations);
		copyOldTransitions(oldPea.getPhases(), newLocations, effectVars);
		connectTrackingAutomaton(newLocations, oldLocations, effectVars, reqSymbolTable,
				new ArrayList<>(oldPea.getClocks()), dcEffectPhase,  effectCdd);
		final List<String> newClocks = new ArrayList<>(oldPea.getClocks());
		final Map<String, String> newVariables = new HashMap<>(oldPea.getVariables());
		newVariables.putAll(mCddTransformer.getTrackingVars());
		final PhaseEventAutomata newPea =
				new PhaseEventAutomata(oldPea.getName() + LOWER_AUTOMATON_SUFFIX, newLocations, newInit, newClocks, newVariables, null);
		mPea2EffectStore.put(newPea, reqEffectStore);
		// remember effect phases and output effect phases
		reqEffectStore.addEffectVars(effectVars);
		getOutputEffectLocations(oldPea, reqEffectStore, effectVars, reqSymbolTable, dcEffectPhase, effectCdd);
		return newPea;
	}

	private static void getOutputEffectLocations(final PhaseEventAutomata oldPea, final ReqEffectStore reqEffectStore,
			final Set<String> effectVars, final IReqSymbolTable reqSymbolTable, final int dcEffectPhase,
			final CDD effectCdd) {
		final Phase[] oldPhases = oldPea.getPhases();
		final List<Phase> phaseList = Arrays.asList(oldPhases);
		for (int i = 0; i < oldPhases.length; i++) {
			final int offset = oldPea.getPhases().length;
			// decide which pea phases have an effect
			final int newEffectLocationIndex = offset + i;
			if (phaseIsEffectPhase(oldPhases[i], dcEffectPhase, effectCdd)) {
				reqEffectStore.addEffectPhaseIndex(newEffectLocationIndex);
				if (!Collections.disjoint(effectVars, reqSymbolTable.getOutputVars())) {
					reqEffectStore.addOutputEffectPhaseIndex(newEffectLocationIndex);
				}
			}
			// decide which pea transitions have an effect
			for (final Transition t : oldPhases[i].getTransitions()) {
				if (isEffectTransition(t.getSrc(), t, dcEffectPhase, effectCdd)) {
					final Integer newTargetPhaseIndex = offset + phaseList.indexOf(t.getDest());
					reqEffectStore.addEffectEdgeIndex(newEffectLocationIndex, newTargetPhaseIndex);
					if (!Collections.disjoint(effectVars, reqSymbolTable.getOutputVars())) {
						reqEffectStore.addOutputEffectEdgeIndex(newEffectLocationIndex, newTargetPhaseIndex);
					}
				}
			}
		}
	}

	private static boolean phaseIsEffectPhase(final Phase location, final int effectDCPhase, final CDD effectCdd) {
		return location.getPhaseBits() != null && location.getPhaseBits().isActive(effectDCPhase)
				&& !location.getPhaseBits().isWaiting(effectDCPhase)
				&& location.getStateInvariant().and(effectCdd.negate()) == CDD.FALSE;
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

	private Phase[] transformLocations(final PatternType pattern, final PhaseEventAutomata oldPea,
			final IReqSymbolTable reqSymbolTable, final CDD effectCdd, final Set<String> effectVars,
			final int effectPhase, DCPhase[] dcFormula) {
		final Phase[] oldPhases = oldPea.getPhases();
		final Phase[] newPhases = new Phase[2 * oldPhases.length];
		for (int i = 0; i < oldPhases.length; i++) {
			final Phase oldPhase = oldPhases[i];
			final boolean isEffectPhase = phaseIsEffectPhase(oldPhases[i], effectPhase, effectCdd);
			// TODO: fit clock invariants to test tracking stuff
			newPhases[i] = new Phase(oldPhase.getName(), oldPhase.getStateInvariant(), oldPhase.getClockInvariant());

			final Set<CDD> activePhaseInvars = getActiveDCPhaseInvariants(oldPhase, dcFormula);
			final Set<String> activePhaseVars = new HashSet<>();
			for (final CDD invar: activePhaseInvars) {
				activePhaseVars.addAll(Req2CauseTrackingCDD.getCddVariables(invar));
			}
			final CDD stateInvariant = mCddTransformer.transformInvariant(oldPhase.getStateInvariant(), effectVars,
					reqSymbolTable.getInputVars(), activePhaseVars, phaseIsEffectPhase(oldPhase, effectPhase, effectCdd));
			final CDD newClockInvariant = mCddTransformer.transformClockInvariant(oldPhase.getClockInvariant(), isEffectPhase);
			final Phase trackingLocation = new Phase(oldPhase.getName() + LOWER_AUTOMATON_SUFFIX, stateInvariant, newClockInvariant );
			newPhases[oldPhases.length + i] = trackingLocation;
			if (oldPhase.isInit) {
				trackingLocation.isInit = true;
			}
		}
		return newPhases;
	}


	private Set<CDD> getActiveDCPhaseInvariants(Phase location, DCPhase[] phases){
		final Set<CDD> activeCDDs = new HashSet<>();
		for(int i = 0; i < phases.length; i++) {
			if (phases[i].getInvariant() == CDD.TRUE || phases[i].getInvariant() == CDD.FALSE) {
				continue;
			}
			if (location.getPhaseBits() == null) {
				mLogger.warn("No phasebits found for location :" + location.toString());
				continue;
			}
			if(location.getPhaseBits().isActive(i) || location.getPhaseBits().isExact(i) || location.getPhaseBits().isWaiting(i)) {
				activeCDDs.add(phases[i].getInvariant());
			}
		}
		return activeCDDs;
	}

	private static int getDCEffectPhaseIndex(final Phase[] oldLocations, final CDD effectCdd) {
		// Find the last phase that is mentioned in automaton. Its the effect phase.
		int lastDcPhase = 0;
		for (int i = 0; i < oldLocations.length; i++) {
			for (final Phase p : oldLocations) {
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

	/*
	 * Connect lower and upper automaton by the following transitions:
	 * - connect every location with its copy in the lower automaton iff upper location is initial
	 * - connect every location in the lower automaton with its copy in the upper automaton iff the location does not
	 *   encode any obligation for the future (i.e. has an edge to the first phase). Add timing bounds so that the
	 *   test generator can not bail to the upper automaton before all obligations are fulfilled.
	 */
	private void connectTrackingAutomaton(final Phase[] newLocations, final Phase[] oldLocations,
			final Set<String> effectVars, final IReqSymbolTable reqSymbolTable, final List<String> clocks,
			int effectDCPhaseId, CDD effectCdd) {
		final int seem = newLocations.length / 2;
		final List<Phase> indexList = Arrays.asList(newLocations);
		// copy edges in first to second automaton
		for (int i = 0; i < seem; i++) {
			for (final Transition trans : newLocations[i].getTransitions()) {
				final int dest = indexList.indexOf(trans.getDest());
				final Phase sourcePhase = newLocations[seem + i];
				final boolean effectTransition = isEffectTransition(sourcePhase, trans, effectDCPhaseId, effectCdd);
				//apply same transformations to CDDs must be done as in the invariants
				final CDD guard = mCddTransformer.transformGurad(mSymbolTable, trans.getGuard(), effectVars,
						Collections.emptySet(), reqSymbolTable.getInputVars(), effectTransition);
				sourcePhase.addTransition(newLocations[seem + dest], guard, trans.getResets());
			}
		}
		// conect the copies
		for (int i = 0; i < seem; i++) {
			CDD clockGuard = CDD.TRUE;
			// check that there is no effect pending when going to the upper automaton
			if (phaseIsEffectPhase(oldLocations[i], i, effectCdd)) {
				final CDD oldInvar = oldLocations[effectDCPhaseId].getClockInvariant();
				clockGuard = mCddTransformer.transformLowerToUpperClockGuard(oldInvar);
			}
			// if there is no edge back to the first phase, there is some obligation to fulfill first
			if (oldLocations[i].getOutgoingTransition(oldLocations[0]) != null) {
				newLocations[seem + i].addTransition(newLocations[i], clockGuard, new String[0]);
			}
			// if the phase is not initial, you shall not switch to the lower automaton (as part of the prefix is not proven)
			if (oldLocations[i].isInit) {
				newLocations[i].addTransition(newLocations[seem + i], CDD.TRUE, clocks.toArray(new String[clocks.size()]));
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
