/*
 * Copyright (C) 2024 Helen Meyer (helen.anna.meyer@gmail.com)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Segment;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.ViolationSequence;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Waypoint;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointAssumption;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointBranching;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointFunctionEnter;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointFunctionReturn;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointTarget;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;

/**
 * Constructs the product automaton of a program automaton and a YAML violation witness.
 *
 * @author Helen Meyer (helen.anna.meyer@gmail.com)
 */
public class YamlWitnessProductAutomaton<LETTER extends IIcfgTransition<?>>
		implements INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> {

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mAbstraction;
	private final Witness mWitness;
	private final ISLPredicate mEmptyStackState;
	private final HashSet<CountingPredicate> mAllCountingStates;

	public YamlWitnessProductAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final Witness witness, final PredicateFactory predicateFactory) {
		mAbstraction = abstraction;
		mWitness = witness;
		mEmptyStackState = predicateFactory.newEmptyStackPredicate();
		mAllCountingStates = new HashSet<>();
	}

	@Deprecated
	@Override
	public IStateFactory<IPredicate> getStateFactory() {
		return mAbstraction.getStateFactory();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mAbstraction.getVpAlphabet();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		final Set<IPredicate> result = new HashSet<>();
		for (final IPredicate s : mAbstraction.getInitialStates()) {
			for (int i = 0; i < mWitness.getEntries().size(); i++) {
				final CountingPredicate countingState = new CountingPredicate(s, 0, i);
				result.add(countingState);
				mAllCountingStates.add(countingState);
			}
		}
		return result;
	}

	@Override
	public boolean isInitial(final IPredicate state) {
		final CountingPredicate annot = (CountingPredicate) state;
		return mAbstraction.isInitial(annot.getUnderlying()) && annot.getWPCounter() == 0;
	}

	@Override
	public boolean isFinal(final IPredicate state) {
		final CountingPredicate annot = (CountingPredicate) state;
		final ViolationSequence vSequence = (ViolationSequence) mWitness.getEntries().get(annot.getVSCounter());

		return (mAbstraction.isFinal(annot.getUnderlying())
				&& (annot.getWPCounter() == (vSequence.getContent().size())));
	}

	@Override
	public int size() {
		return mAllCountingStates.size();
	}

	@Override
	public String sizeInformation() {
		return mAbstraction.sizeInformation();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, IPredicate>> internalSuccessors(final IPredicate state,
			final LETTER letter) {
		final CountingPredicate countingState = (CountingPredicate) state;
		final IPredicate currentUnderlying = countingState.getUnderlying();
		int currentCounter = countingState.getWPCounter();

		final ArrayList<OutgoingInternalTransition<LETTER, IPredicate>> counterSuccessors = new ArrayList<>();

		// return successors with the same counter if witness has been fully read
		if (isWitnessFinished(currentCounter, countingState.getVSCounter())) {
			counterSuccessors.addAll(getInternalCounterSuccessors(currentUnderlying, letter, currentCounter,
					countingState.getVSCounter()));
			return counterSuccessors;
		}

		final ViolationSequence currentvSeq =
				(ViolationSequence) mWitness.getEntries().get(countingState.getVSCounter());
		Segment currentSegment = currentvSeq.getContent().get(currentCounter);
		Waypoint currentWP = currentSegment.getFollow();

		// return empty List if an avoid WP matches (Assumptions are ignored)
		if (currentSegment.getAvoid().stream().anyMatch(x -> matchesInternal(letter, x))) {
			return List.of();
		}

		// for Assumption Waypoints continue with the same state but increase the counter
		while (currentWP instanceof WaypointAssumption && matchesLocation(letter, currentWP)) {
			currentCounter++;
			currentSegment = currentvSeq.getContent().get(currentCounter);
			currentWP = currentSegment.getFollow();
			if (currentSegment.getAvoid().stream().anyMatch(x -> matchesInternal(letter, x))) {
				return List.of();
			}
		}

		if (matchesInternal(letter, currentWP)) {
			currentCounter++;
		}

		counterSuccessors.addAll(
				getInternalCounterSuccessors(currentUnderlying, letter, currentCounter, countingState.getVSCounter()));

		return counterSuccessors;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, IPredicate>> callSuccessors(final IPredicate state,
			final LETTER letter) {
		final CountingPredicate countingState = (CountingPredicate) state;
		final IPredicate currentUnderlying = countingState.getUnderlying();
		int currentCounter = countingState.getWPCounter();
		final ArrayList<OutgoingCallTransition<LETTER, IPredicate>> counterSuccessors = new ArrayList<>();

		if (isWitnessFinished(currentCounter, countingState.getVSCounter())) {
			counterSuccessors.addAll(
					getCallCounterSuccessors(currentUnderlying, letter, currentCounter, countingState.getVSCounter()));
			return counterSuccessors;
		}

		final ViolationSequence currentvSeq =
				(ViolationSequence) mWitness.getEntries().get(countingState.getVSCounter());
		Segment currentSegment = currentvSeq.getContent().get(currentCounter);
		Waypoint currentWP = currentSegment.getFollow();

		if (currentSegment.getAvoid().stream().anyMatch(x -> matchesCall(letter, x))) {
			return List.of();
		}

		while (currentWP instanceof WaypointAssumption && matchesLocation(letter, currentWP)) {
			currentCounter++;
			currentSegment = currentvSeq.getContent().get(currentCounter);
			currentWP = currentSegment.getFollow();
			if (currentSegment.getAvoid().stream().anyMatch(x -> matchesInternal(letter, x))) {
				return List.of();
			}
		}

		if (matchesCall(letter, currentWP)) {
			currentCounter++;
		}

		counterSuccessors.addAll(
				getCallCounterSuccessors(currentUnderlying, letter, currentCounter, countingState.getVSCounter()));

		return counterSuccessors;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final LETTER letter) {
		final CountingPredicate countingState = (CountingPredicate) state;
		final CountingPredicate countingHier = (CountingPredicate) hier;
		final IPredicate currentUnderlying = countingState.getUnderlying();
		int currentCounter = countingState.getWPCounter();

		final ArrayList<OutgoingReturnTransition<LETTER, IPredicate>> counterSuccessors = new ArrayList<>();

		if (isWitnessFinished(currentCounter, countingState.getVSCounter())) {
			counterSuccessors.addAll(getReturnCounterSuccessors(currentUnderlying, countingHier, letter, currentCounter,
					countingState.getVSCounter()));
			return counterSuccessors;
		}
		final ViolationSequence currentvSeq =
				(ViolationSequence) mWitness.getEntries().get(countingState.getVSCounter());
		Segment currentSegment = currentvSeq.getContent().get(currentCounter);
		Waypoint currentWP = currentSegment.getFollow();

		if (currentSegment.getAvoid().stream().anyMatch(x -> matchesCall(letter, x))) {
			return List.of();
		}

		while (currentWP instanceof WaypointAssumption && matchesLocation(letter, currentWP)) {
			currentCounter++;
			currentSegment = currentvSeq.getContent().get(currentCounter);
			currentWP = currentSegment.getFollow();
			if (currentSegment.getAvoid().stream().anyMatch(x -> matchesInternal(letter, x))) {
				return List.of();
			}
		}

		if (matchesReturn(letter, currentWP)) {
			currentCounter++;
		}
		counterSuccessors.addAll(getReturnCounterSuccessors(currentUnderlying, countingHier, letter, currentCounter,
				countingState.getVSCounter()));
		return counterSuccessors;
	}

	private ArrayList<OutgoingInternalTransition<LETTER, IPredicate>> getInternalCounterSuccessors(
			final IPredicate state, final LETTER letter, final int counter, final int vsCounter) {
		final ArrayList<OutgoingInternalTransition<LETTER, IPredicate>> counterSuccessors = new ArrayList<>();
		final Iterable<OutgoingInternalTransition<LETTER, IPredicate>> noCounterSuccessors =
				mAbstraction.internalSuccessors(state, letter);
		for (final OutgoingInternalTransition<LETTER, IPredicate> outTrans : noCounterSuccessors) {
			final CountingPredicate counterSuccessor = new CountingPredicate(outTrans.getSucc(), counter, vsCounter);
			counterSuccessors.add(new OutgoingInternalTransition<>(outTrans.getLetter(), counterSuccessor));
			mAllCountingStates.add(counterSuccessor);
		}
		return counterSuccessors;
	}

	private ArrayList<OutgoingCallTransition<LETTER, IPredicate>> getCallCounterSuccessors(final IPredicate state,
			final LETTER letter, final int counter, final int vsCounter) {
		final ArrayList<OutgoingCallTransition<LETTER, IPredicate>> counterSuccessors = new ArrayList<>();
		final Iterable<OutgoingCallTransition<LETTER, IPredicate>> noCounterSuccessors =
				mAbstraction.callSuccessors(state, letter);
		for (final OutgoingCallTransition<LETTER, IPredicate> outTrans : noCounterSuccessors) {
			final CountingPredicate counterSuccessor = new CountingPredicate(outTrans.getSucc(), counter, vsCounter);
			counterSuccessors.add(new OutgoingCallTransition<>(outTrans.getLetter(), counterSuccessor));
			mAllCountingStates.add(counterSuccessor);
		}
		return counterSuccessors;
	}

	private ArrayList<OutgoingReturnTransition<LETTER, IPredicate>> getReturnCounterSuccessors(final IPredicate state,
			final CountingPredicate hier, final LETTER letter, final int counter, final int vsCounter) {
		final ArrayList<OutgoingReturnTransition<LETTER, IPredicate>> counterSuccessors = new ArrayList<>();
		final Iterable<OutgoingReturnTransition<LETTER, IPredicate>> noCounterSuccessors =
				mAbstraction.returnSuccessors(state, hier.getUnderlying(), letter);
		for (final OutgoingReturnTransition<LETTER, IPredicate> outTrans : noCounterSuccessors) {
			final CountingPredicate counterSuccessor = new CountingPredicate(outTrans.getSucc(), counter, vsCounter);
			counterSuccessors.add(new OutgoingReturnTransition<>(hier, outTrans.getLetter(), counterSuccessor));
			mAllCountingStates.add(counterSuccessor);
		}
		return counterSuccessors;
	}

	private boolean matchesInternal(final LETTER statement, final Waypoint waypoint) {
		if (matchesLocation(statement, waypoint)) {
			if (waypoint instanceof WaypointBranching) {
				final ConditionAnnotation conditionAnnot = ConditionAnnotation.getAnnotation(statement);
				if (conditionAnnot == null) {
					return false;
				}
				if (waypoint.getConstraint().getValue().equals("false")) {
					return conditionAnnot.isNegated();

				}
				if (waypoint.getConstraint().getValue().equals("true")) {
					return !conditionAnnot.isNegated();
				}
			}
			if (waypoint instanceof WaypointTarget) {
				return true;
			}
		}
		return false;
	}

	private boolean matchesCall(final LETTER statement, final Waypoint waypoint) {
		final ILocation programLoc = ILocation.getAnnotation(statement);
		final Location witnessLoc = waypoint.getLocation();
		if (waypoint instanceof WaypointFunctionEnter && programLoc.getEndLine() == witnessLoc.getLine()) {
			if (witnessLoc.getColumn() == null) {
				return true;
			}
			if (witnessLoc.getColumn() == programLoc.getEndColumn()) {
				return true;
			}
		}
		return false;
	}

	private boolean matchesReturn(final LETTER statement, final Waypoint waypoint) {
		final var call = ((IIcfgReturnTransition<?, ?>) statement).getCorrespondingCall();
		final ILocation hierLoc = ILocation.getAnnotation(call);
		final Location witnessLoc = waypoint.getLocation();
		if (hierLoc != null && hierLoc.getEndLine() == witnessLoc.getLine()
				&& waypoint instanceof WaypointFunctionReturn) {
			if (witnessLoc.getColumn() == null) {
				return true;
			}
			if (witnessLoc.getColumn() == hierLoc.getEndColumn()) {
				return true;
			}
		}

		return false;
	}

	private boolean matchesLocation(final LETTER statement, final Waypoint waypoint) {
		final ILocation programLoc = ILocation.getAnnotation(statement);
		final Location witnessLoc = waypoint.getLocation();
		if (programLoc.getStartLine() == witnessLoc.getLine()) {
			if (witnessLoc.getColumn() == null) {
				return true;
			}
			if (witnessLoc.getColumn() == programLoc.getStartColumn()) {
				return true;
			}
		}
		return false;
	}

	private boolean isWitnessFinished(final int counter, final int vsCounter) {
		final ViolationSequence vSeq = (ViolationSequence) mWitness.getEntries().get(vsCounter);
		return counter >= vSeq.getContent().size();
	}

	private static final class CountingPredicate extends AnnotatedPredicate<IPredicate, Pair<Integer, Integer>>
			implements ISLPredicate {
		public CountingPredicate(final IPredicate underlying, final int wpCounter, final int vsCounter) {
			super(underlying, new Pair<>(wpCounter, vsCounter));
		}

		public int getWPCounter() {
			return mAnnotation.getFirst();

		}

		public int getVSCounter() {
			return mAnnotation.getSecond();
		}

		@Override
		public IcfgLocation getProgramPoint() {
			return ((ISLPredicate) mUnderlying).getProgramPoint();
		}
	}
}
