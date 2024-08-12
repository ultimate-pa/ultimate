/*
 * Copyright (C) 2020 Vincent Langenfeld <langenfv@tf.uni-freiburg.de>
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.InitialTransition;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseBits;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Vincent Langenfeld <langenfv@tf.uni-freiburg.de>
 *
 */
public class Req2CauseTrackingPea implements IReq2Pea {

	private final ILogger mLogger;
	private final List<DeclarationPattern> mInitPattern;
	private final List<ReqPeas> mReqPeas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Map<PhaseEventAutomata, ReqEffectStore> mPea2EffectStore;
	private final Req2CauseTrackingCDD mCddTransformer;
	private final Durations mDurations;

	private static final String LOWER_AUTOMATON_SUFFIX = "_tt";

	public Req2CauseTrackingPea(final IUltimateServiceProvider services, final ILogger logger,
			final List<DeclarationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mPea2EffectStore = new HashMap<>();
		mReqPeas = new ArrayList<>();
		mCddTransformer = new Req2CauseTrackingCDD(mLogger);
		mDurations = new Durations();
	}

	@Override
	public void transform(final IReq2Pea req2pea) {
		final List<ReqPeas> simplePeas = req2pea.getReqPeas();
		final IReqSymbolTable oldSymbolTable = req2pea.getSymboltable();
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mServices, mLogger);
		for (final DeclarationPattern p : mInitPattern) {
			builder.addInitPattern(p);
			mDurations.addInitPattern(p);
			if (p.getCategory() == VariableCategory.OUT) {
				builder.addAuxvar(ReqTestAnnotator.getTrackingVar(p.getId()), "bool", p);
			}
		}
		for (final ReqPeas reqpea : simplePeas) {
			final PatternType<?> pattern = reqpea.getPattern();
			mDurations.addNonInitPattern(pattern);
			final List<Entry<CounterTrace, PhaseEventAutomata>> ct2pea = reqpea.getCounterTrace2Pea();
			final List<Entry<CounterTrace, PhaseEventAutomata>> newCt2pea = new ArrayList<>(ct2pea.size());
			for (final Entry<CounterTrace, PhaseEventAutomata> pea : ct2pea) {
				final PhaseEventAutomata newPea =
						transformPea(pattern, pea.getValue(), oldSymbolTable, pea.getKey().getPhases());
				newCt2pea.add(new Pair<>(pea.getKey(), newPea));
				builder.addPea(pattern, newPea);
			}
			mReqPeas.add(new ReqPeas(pattern, newCt2pea));
		}
		// builder.addAuxvar(mLocation, ReqTestAnnotator.INITIAL_STEP_FLAG , "bool");
		mSymbolTable = builder.constructSymbolTable();
	}

	/*
	 * Make two copies of the peas that are connected by Transitions from each state to its copy. The upper automaton
	 * (lower half of the array of Locations) prevents bad things from happening i.e. only accepts runs that do not
	 * violate the requirement. The lower automaton (upper half of the array) keeps information over the determindness
	 * of all variables.
	 */
	private PhaseEventAutomata transformPea(final PatternType<?> pattern, final PhaseEventAutomata oldPea,
			final IReqSymbolTable oldSymbolTable, final DCPhase[] dcFormula) {
		final CDD effectCdd = Req2CauseTrackingCDD.getEffectCDD(pattern);
		final Set<String> effectVars = Req2CauseTrackingCDD.getCddVariables(effectCdd);
		effectVars.removeAll(oldSymbolTable.getConstVars());
		// TODO: final Set<String> effectVars = mCddTransformer.getEffectVariables(pattern, id2bounds);
		// repair old pea
		setFlags(oldPea.getInit());
		final List<Phase> oldLocations = oldPea.getPhases();
		final int dcEffectPhase = getHighestDCPhase(oldLocations, dcFormula);
		mLogger.info(new StringBuilder("Effect Variables of ").append(pattern.toString()).append(": ")
				.append(effectVars.toString()).toString() + ", with effect phase: " + Integer.toString(dcEffectPhase));
		final List<Phase> newLocations =
				transformLocations(oldPea, oldSymbolTable, effectVars, dcEffectPhase, dcFormula);
		final List<Phase> newInit = getInitialLocations(oldLocations);
		copyOldTransitions(oldPea.getPhases(), newLocations);
		copyTransitionsToLower(oldLocations, newLocations, effectVars, oldSymbolTable, dcEffectPhase, effectCdd);
		connectUpperToLowerAutomaton(newLocations, oldLocations, new ArrayList<>(oldPea.getClocks()), dcEffectPhase);
		final List<String> newClocks = new ArrayList<>(oldPea.getClocks());
		final Map<String, String> newVariables = new HashMap<>(oldPea.getVariables());
		newVariables.putAll(mCddTransformer.getTrackingVars());
		final PhaseEventAutomata newPea =
				new PhaseEventAutomata(oldPea.getName() + LOWER_AUTOMATON_SUFFIX, newLocations,
						newInit.stream().map(x -> new InitialTransition(CDD.TRUE, x)).collect(Collectors.toList()),
						newClocks, newVariables, null);
		final ReqEffectStore reqEffectStore = new ReqEffectStore();
		reqEffectStore.addEffectVars(effectVars);
		// remember effect phases and output effect phases
		getOutputEffectLocations(oldPea, reqEffectStore, effectVars, oldSymbolTable, dcEffectPhase, effectCdd);
		mPea2EffectStore.put(newPea, reqEffectStore);
		return newPea;
	}

	private static void getOutputEffectLocations(final PhaseEventAutomata oldPea, final ReqEffectStore reqEffectStore,
			final Set<String> effectVars, final IReqSymbolTable oldSymbolTable, final int dcEffectPhase,
			final CDD effectCdd) {
		final List<Phase> oldPhases = oldPea.getPhases();
		final List<Phase> phaseList = oldPhases;
		for (int i = 0; i < oldPhases.size(); i++) {
			final int offset = oldPea.getPhases().size();
			// decide which pea phases have an effect
			final int newEffectLocationIndex = offset + i;
			if (isEffectLocation(oldPhases.get(i), dcEffectPhase)) {
				reqEffectStore.addEffectPhaseIndex(newEffectLocationIndex);
				if (!Collections.disjoint(effectVars, oldSymbolTable.getOutputVars())) {
					reqEffectStore.addOutputEffectPhaseIndex(newEffectLocationIndex);
				}
			}
			// decide which pea transitions have an effect
			for (final Transition t : oldPhases.get(i).getTransitions()) {
				if (isEffectTransition(t.getSrc(), t, dcEffectPhase, effectCdd)) {
					final Integer newTargetPhaseIndex = offset + phaseList.indexOf(t.getDest());
					reqEffectStore.addEffectEdgeIndex(newEffectLocationIndex, newTargetPhaseIndex);
					if (!Collections.disjoint(effectVars, oldSymbolTable.getOutputVars())) {
						reqEffectStore.addOutputEffectEdgeIndex(newEffectLocationIndex, newTargetPhaseIndex);
					}
				}
			}
		}
	}

	private static boolean isEffectLocation(final Phase location, final int effectDCPhaseIndex) {
		if (location.getPhaseBits() == null) {
			return false;
		}
		final PhaseBits pb = location.getPhaseBits();
		return (pb.isActive(effectDCPhaseIndex) && !pb.isWaiting(effectDCPhaseIndex)) || pb.isExact(effectDCPhaseIndex);
	}

	private static boolean isEffectTransition(final Phase source, final Transition transition, final int effectDCPhase,
			final CDD effectCdd) {
		return source.getPhaseBits() != null && source.getPhaseBits().isActive(effectDCPhase)
				&& transition.getGuard().and(effectCdd.negate().prime(Collections.emptySet())) == CDD.FALSE;
	}

	private static void setFlags(final List<Phase> initialPhases) {
		for (final Phase p : initialPhases) {
			p.isInit = true;
		}
	}

	private List<Phase> transformLocations(final PhaseEventAutomata oldPea, final IReqSymbolTable reqSymbolTable,
			final Set<String> effectVars, final int effectPhase, final DCPhase[] dcFormula) {
		final List<Phase> oldPhases = oldPea.getPhases();
		final List<Phase> newPhases = new ArrayList<>();
		for (int i = 0; i < oldPhases.size(); i++) {
			final Phase oldPhase = oldPhases.get(i);

			// get tracking vars according to phases in location
			final Set<String> trackThoseVars = getAllToTrackVars(oldPhase, dcFormula, effectPhase, effectVars);
			trackThoseVars.removeAll(reqSymbolTable.getConstVars());
			trackThoseVars.removeAll(reqSymbolTable.getInputVars());

			// final CDD upperStateInvar = mCddTransformer.transformInvariantUpper(oldPhase.getStateInvariant(),
			// effectVars,
			// reqSymbolTable.getInputVars(), reqSymbolTable.getConstVars(), activePhaseVars, isEffectLocation(oldPhase,
			// effectPhase));
			final CDD upperStateInvar = oldPhase.getStateInvariant();
			newPhases.set(i, new Phase(oldPhase.getName(), upperStateInvar, oldPhase.getClockInvariant()));

			final CDD trackingStateInvar = mCddTransformer.transformInvariantTracking(oldPhase.getStateInvariant(),
					trackThoseVars, effectVars, isEffectLocation(oldPhase, effectPhase));
			final Phase trackingLocation = new Phase(oldPhase.getName() + LOWER_AUTOMATON_SUFFIX, trackingStateInvar,
					oldPhase.getClockInvariant());
			newPhases.set(oldPhases.size() + i, trackingLocation);
			if (oldPhase.isInit) {
				trackingLocation.isInit = true;
			}
		}
		return newPhases;
	}

	private static Set<String> getAllToTrackVars(final Phase location, final DCPhase[] dcFormula, final int effectPhase,
			final Set<String> effectVars) {
		final Set<String> toTrackVars = new HashSet<>();
		final PhaseBits pb = location.getPhaseBits();
		final CDD effectCDD = dcFormula[effectPhase].getInvariant();
		if (pb == null) {
			return Collections.emptySet();
		}
		for (int i = 0; i < dcFormula.length; i++) {
			if ((pb.isActive(i) && !pb.isWaiting(i)) || pb.isExact(i)) {
				final CDD invar = dcFormula[i].getInvariant();
				final Set<String> cddVars = Req2CauseTrackingCDD.getCddVariables(invar);
				// if the prior to last phase is a true phase, look ahead and see what we have to do to NOT
				// enter the effect phase on accident
				if (invar == CDD.TRUE && i == effectPhase) {
					cddVars.addAll(Req2CauseTrackingCDD.getCddVariables(dcFormula[i + 1].getInvariant()));
				}
				if (effectPhase == i) {
					// if this phase is also an effect phase then remove all effect vars from the phases vars
					cddVars.removeAll(effectVars);
				}
				if (pb.isWaiting(effectPhase)) {
					// we are waiting for the effect to happen so do not try to prove absence of effect
					final Set<Decision<?>> effectObservables = Req2CauseTrackingCDD.getDecisions(effectCDD);
					final Set<Decision<?>> invarObservables = Req2CauseTrackingCDD.getDecisions(invar);
					invarObservables.removeAll(effectObservables);
					cddVars.retainAll(Req2CauseTrackingCDD.getCddVariables(invarObservables));
				}
				toTrackVars.addAll(cddVars);
			}
		}
		return toTrackVars;
	}

	private static int getHighestDCPhase(final List<Phase> oldLocations, final DCPhase[] dcFormula) {
		// Find the last phase that is mentioned in automaton. Its the effect phase.
		int lastDcPhase = 0;
		for (int i = 0; i < dcFormula.length; i++) {
			for (final Phase p : oldLocations) {
				final PhaseBits pb = p.getPhaseBits();
				if (pb != null && (pb.isActive(i) || pb.isWaiting(i) || pb.isExact(i)) && i > lastDcPhase) {
					lastDcPhase = i;
				}
			}
		}

		return lastDcPhase;
	}

	private static List<Phase> getInitialLocations(final List<Phase> phases) {
		final List<Phase> initialPhases = new ArrayList<>();
		for (final Phase p : phases) {
			if (p.isInit) {
				initialPhases.add(p);
			}
		}
		return initialPhases;
	}

	private static void copyOldTransitions(final List<Phase> oldPhases, final List<Phase> newLocations) {
		final List<Phase> indexList = oldPhases;
		for (int i = 0; i < oldPhases.size(); i++) {
			for (final Transition trans : oldPhases.get(i).getTransitions()) {
				final int dest = indexList.indexOf(trans.getDest());
				newLocations.get(i).addTransition(newLocations.get(dest), trans.getGuard(), trans.getResets());
			}
		}
	}

	/*
	 * Copy all transitions from the upper automaton to the lower automaton. Add tracking guards and clock
	 * transformations in the process.
	 */
	private void copyTransitionsToLower(final List<Phase> oldLocations, final List<Phase> newLocations,
			final Set<String> effectVars, final IReqSymbolTable reqSymbolTable, final int effectDCPhaseId,
			final CDD effectCdd) {
		final int seem = newLocations.size() / 2;
		final List<Phase> indexList = newLocations;
		// copy edges in first to second automaton
		for (int i = 0; i < seem; i++) {
			for (final Transition trans : newLocations.get(i).getTransitions()) {
				final int dest = indexList.indexOf(trans.getDest());
				final Phase sourcePhase = newLocations.get(seem + 1);
				final boolean effectTransition = isEffectTransition(sourcePhase, trans, effectDCPhaseId, effectCdd);
				// add tracking variables to cdds on the edge
				CDD guard = mCddTransformer.transformGurad(trans.getGuard(), effectVars, reqSymbolTable.getInputVars(),
						reqSymbolTable.getConstVars(), effectTransition);
				// add time bound in lower automaton if effect phase has an upper bound
				final PhaseBits pbSource = oldLocations.get(i).getPhaseBits();
				final PhaseBits pbDest = oldLocations.get(dest).getPhaseBits();
				if (pbSource != null && pbSource.isWaiting(effectDCPhaseId) &&
				// if pbDest is null, it is a sink state after having waited
						(pbDest == null || !pbDest.isWaiting(effectDCPhaseId))) {
					guard = guard.and(mCddTransformer.upperToLowerBoundCdd(sourcePhase.getClockInvariant(), true));
				}
				sourcePhase.addTransition(newLocations.get(seem + 1), guard, trans.getResets());

			}
		}
	}

	/*
	 * Connect lower and upper automaton by the following transitions: - connect every location with its copy in the
	 * lower automaton iff upper location is initial - connect every location in the lower automaton with its copy in
	 * the upper automaton iff the location does not encode any obligation for the future (i.e. has an edge to the first
	 * phase). Add timing bounds so that the test generator can not bail to the upper automaton before all obligations
	 * are fulfilled.
	 */
	private void connectUpperToLowerAutomaton(final List<Phase> newLocations, final List<Phase> oldLocations,
			final List<String> clocks, final int effectDCPhaseId) {
		final int seem = newLocations.size() / 2;
		for (int i = 0; i < seem; i++) {
			CDD clockGuard = CDD.TRUE;
			if (isEffectLocation(oldLocations.get(i), effectDCPhaseId)) {
				final CDD oldClockInvar = oldLocations.get(i).getClockInvariant();
				clockGuard = mCddTransformer.upperToLowerBoundCdd(oldClockInvar, false);
			}
			if (oldLocations.get(i).getOutgoingTransition(oldLocations.get(0)) != null) {
				newLocations.get(seem + 1).addTransition(newLocations.get(i), clockGuard, new String[0]);
			}
			if (oldLocations.get(i).isInit) {
				newLocations.get(i).addTransition(newLocations.get(seem + 1), CDD.TRUE,
						clocks.toArray(new String[clocks.size()]));
			}
		}
	}

	public Map<PhaseEventAutomata, ReqEffectStore> getReqEffectStore() {
		return mPea2EffectStore;
	}

	@Override
	public List<ReqPeas> getReqPeas() {
		return mReqPeas;
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}

	public Map<PhaseEventAutomata, ReqEffectStore> getEffectStore() {
		return mPea2EffectStore;
	}

	@Override
	public boolean hasErrors() {
		return mHasErrors;
	}

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		return new ReqTestAnnotator(mServices, mLogger, this);
	}

	@Override
	public Durations getDurations() {
		return mDurations;
	}

}
