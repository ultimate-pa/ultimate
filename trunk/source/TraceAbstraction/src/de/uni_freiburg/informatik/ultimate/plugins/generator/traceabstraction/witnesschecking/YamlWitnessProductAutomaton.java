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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
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
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

/**
 * Constructs the product automaton of a program automaton and a YAML violation witness.
 *
 * @author Helen Meyer (helen.anna.meyer@gmail.com)
 */
public class YamlWitnessProductAutomaton<LETTER extends IIcfgTransition<?>>
		implements INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> {

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mAbstraction;
	private final Witness mWitness;
	private final PredicateFactory mPredicateFactory;
	private final ISLPredicate mEmptyStackState;

	public YamlWitnessProductAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final Witness witness, final PredicateFactory predicateFactory) {
		mAbstraction = abstraction;
		mWitness = witness;
		mPredicateFactory = predicateFactory;
		mEmptyStackState = predicateFactory.newEmptyStackPredicate();
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
			result.add(new CountingPredicate(s, 0));
		}
		return result;
	}

	@Override
	public boolean isInitial(final IPredicate state) {
		final CountingPredicate annot = (CountingPredicate) state;
		return mAbstraction.isInitial(annot.getUnderlying()) && annot.getCounter() == 0;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean isFinal(final IPredicate state) {
		final CountingPredicate annot = (CountingPredicate) state;
		final ViolationSequence vSequence = (ViolationSequence) mWitness.getEntries().get(0);

		return (mAbstraction.isFinal(annot.getUnderlying()) && annot.getCounter() == vSequence.getContent().size());
	}

	@Override
	public int size() {
		// TODO: Can we get a more precise size?
		return mAbstraction.size();
	}

	@Override
	public String sizeInformation() {
		// TODO: Can we get a more precise size?
		return mAbstraction.sizeInformation();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, IPredicate>> internalSuccessors(final IPredicate state,
			final LETTER letter) {
		final CountingPredicate countingState = (CountingPredicate) state;
		final ArrayList<OutgoingInternalTransition<LETTER, IPredicate>> CounterSuccessors = new ArrayList<>();
		final Iterable<OutgoingInternalTransition<LETTER, IPredicate>> noCounterSuccessors =
				mAbstraction.internalSuccessors(countingState.getUnderlying(), letter);

		final ViolationSequence currentvSeq = (ViolationSequence) mWitness.getEntries().get(0);
		final Segment currentSegment = currentvSeq.getContent().get(countingState.getCounter());
		final Waypoint currentWP = currentSegment.getFollow();

		if (currentSegment.getAvoid().stream().anyMatch(x -> matchesInternal(letter, x, null))) {
			return CounterSuccessors;
		}
		for (final OutgoingInternalTransition<LETTER, IPredicate> outTrans : noCounterSuccessors) {
			if (matchesInternal(letter, currentWP, outTrans.getSucc())) {
				final CountingPredicate counterSuccessor =
						new CountingPredicate(outTrans.getSucc(), countingState.getCounter() + 1);

				CounterSuccessors.add(new OutgoingInternalTransition<>(outTrans.getLetter(), counterSuccessor));
			}
			final CountingPredicate counterSuccessor =
					new CountingPredicate(outTrans.getSucc(), countingState.getCounter());

			CounterSuccessors.add(new OutgoingInternalTransition<>(outTrans.getLetter(), counterSuccessor));

		}
		return CounterSuccessors;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, IPredicate>> callSuccessors(final IPredicate state,
			final LETTER letter) {
		final CountingPredicate countingState = (CountingPredicate) state;
		final ArrayList<OutgoingCallTransition<LETTER, IPredicate>> CounterSuccessors = new ArrayList<>();
		final Iterable<OutgoingCallTransition<LETTER, IPredicate>> noCounterSuccessors =
				mAbstraction.callSuccessors(countingState.getUnderlying(), letter);

		for (final WitnessEntry entry : mWitness.getEntries()) {
			if (entry instanceof ViolationSequence) {
				final ViolationSequence vSeq = (ViolationSequence) entry;
				Integer i = 0;
				while (i < vSeq.getContent().size()) {
					final Waypoint currentWP = vSeq.getContent().get(i).getFollow();
					if (matches(letter, currentWP)) {
						for (final OutgoingCallTransition<LETTER, IPredicate> outTrans : noCounterSuccessors) {
							final CountingPredicate counterSuccessor =
									new CountingPredicate(outTrans.getSucc(), countingState.getCounter() + 1);

							CounterSuccessors.add(new OutgoingCallTransition<>(outTrans.getLetter(), counterSuccessor));
						}
					}
					i++;
				}
			}
		}
		return CounterSuccessors;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final LETTER letter) {
		final CountingPredicate countingState = (CountingPredicate) state;
		final ArrayList<OutgoingReturnTransition<LETTER, IPredicate>> CounterSuccessors = new ArrayList<>();
		final Iterable<OutgoingReturnTransition<LETTER, IPredicate>> noCounterSuccessors =
				mAbstraction.returnSuccessors(countingState.getUnderlying(), hier, letter);

		for (final WitnessEntry entry : mWitness.getEntries()) {
			if (entry instanceof ViolationSequence) {
				final ViolationSequence vSeq = (ViolationSequence) entry;
				Integer i = 0;
				while (i < vSeq.getContent().size()) {
					final Waypoint currentWP = vSeq.getContent().get(i).getFollow();
					if (matches(letter, currentWP)) {
						for (final OutgoingReturnTransition<LETTER, IPredicate> outTrans : noCounterSuccessors) {
							final CountingPredicate counterSuccessor =
									new CountingPredicate(outTrans.getSucc(), countingState.getCounter() + 1);

							CounterSuccessors.add(new OutgoingReturnTransition<>(outTrans.getHierPred(),
									outTrans.getLetter(), counterSuccessor));
						}
					}
					i++;
				}
			}
		}
		return CounterSuccessors;
	}

	private boolean matchesInternal(final LETTER statement, final Waypoint waypoint, final IPredicate state) {
		final ILocation programLoc = ILocation.getAnnotation(statement);
		final Location witnessLoc = waypoint.getLocation();
		if (programLoc.getStartLine() == witnessLoc.getLine()) {
			if (waypoint instanceof WaypointAssumption) {
				return true;
			}
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
			if (waypoint instanceof WaypointTarget && mAbstraction.isFinal(state)) {
				return true;
			}
		}

		return false;
	}

	private boolean matches(final LETTER statement, final Waypoint waypoint) {
		final ILocation programLoc = ILocation.getAnnotation(statement);
		final Location witnessLoc = waypoint.getLocation();
		if (programLoc.getStartLine() == witnessLoc.getLine()) {
			// TODO: This is not quite how the matching should work. We need to consider the waypoint type and the
			// column
			// (that might also be slightly adjusted).
			if (waypoint instanceof WaypointAssumption) {
				// TODO
			}
			if (waypoint instanceof WaypointBranching) {
				// TODO
				if (waypoint.getConstraint().getValue().equals("false")) {
					//
				}
				if (waypoint.getConstraint().getValue().equals("true")) {
					//
				}
			}

			if (waypoint instanceof WaypointFunctionEnter) {
				// TODO
			}
			if (waypoint instanceof WaypointFunctionReturn) {
				// TODO
			}
			if (waypoint instanceof WaypointTarget) {
				// TODO
			}
			return true;
		}

		return false;
	}

	private static final class CountingPredicate extends AnnotatedPredicate<IPredicate, Integer> {
		public CountingPredicate(final IPredicate underlying, final int counter) {
			super(underlying, counter);
		}

		public int getCounter() {
			return mAnnotation;
		}
	}
}
