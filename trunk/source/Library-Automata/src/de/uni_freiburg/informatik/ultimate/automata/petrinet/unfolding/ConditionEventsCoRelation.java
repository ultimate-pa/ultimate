/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;

/**
 * A co-relation between a {@link Condition} and an {@link Event}.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public class ConditionEventsCoRelation<LETTER, PLACE> implements ICoRelation<LETTER, PLACE> {
	private static final boolean EXTENDED_ASSERTION_CHECKING = false;
	private long mQueryCounterYes;
	private long mQueryCounterNo;

	/**
	 * TODO schaetzc 2018-08-16: This does not seem to store all co-relations between conditions and events. Document
	 * which subset is stored. For [1] the co-relation between the only a-event and all p3-conditions were missing. [1]
	 * trunk/examples/Automata/regression/pn/operations/removeDead/VitalParallel.ats TODO Matthias 2019-09-25: I just
	 * checked this and saw all three p3-conditions in relation with the (only) a-event. Maybe the problem has been
	 * fixed in the last 13 months.
	 */
	private final HashRelation3<Condition<LETTER, PLACE>, Transition<LETTER, PLACE>, Event<LETTER, PLACE>> mCoRelation =
			new HashRelation3<>();
	private final BranchingProcess<LETTER, PLACE> mBranchingProcess;

	/**
	 * Constructor.
	 *
	 * @param branchingProcess
	 *            branching process
	 */
	public ConditionEventsCoRelation(final BranchingProcess<LETTER, PLACE> branchingProcess) {
		mBranchingProcess = branchingProcess;
	}

	@Override
	public long getQueryCounterYes() {
		return mQueryCounterYes;
	}

	@Override
	public long getQueryCounterNo() {
		return mQueryCounterNo;
	}

	@Override
	public void initialize(final Set<Condition<LETTER, PLACE>> initialConditions) {
		// there are no events the conditions could be in relation with yet.
		// hence there's nothing to do here
	}

	private Stream<Event<LETTER, PLACE>> streamCoRelatedEvents(final Condition<LETTER, PLACE> c) {
		return streamCoRelatedEvents(c, mCoRelation.projectToSnd(c));
	}

	private Stream<Event<LETTER, PLACE>> streamCoRelatedEvents(final Condition<LETTER, PLACE> c,
			final Set<Transition<LETTER, PLACE>> transitions) {
		return transitions.stream().flatMap(t -> mCoRelation.projectToTrd(c, t).stream());
	}

	private Stream<Condition<LETTER, PLACE>> streamCoRelatedConditions(final Condition<LETTER, PLACE> c) {
		return streamCoRelatedConditions(c, mCoRelation.projectToSnd(c));
	}

	/**
	 * @return Stream of all conditions that are
	 *         <ul>
	 *         <li>in the condition marking of c's predecessor event or
	 *         <li>in co-relation to the {@link Condition} c and whose predecessor is an event whose transition is in
	 *         the given set.
	 *         </ul>
	 */
	private Stream<Condition<LETTER, PLACE>> streamCoRelatedConditions(final Condition<LETTER, PLACE> c,
			final Set<Transition<LETTER, PLACE>> transitions) {
		return Stream.concat(c.getPredecessorEvent().getConditionMark().stream(),
				streamCoRelatedEvents(c, transitions).flatMap(x -> x.getSuccessorConditions().stream()));
	}

	private Stream<Condition<LETTER, PLACE>> streamNonCutoffCoRelatedConditions(final Condition<LETTER, PLACE> c) {
		return streamNonCutoffCoRelatedConditions(c, mCoRelation.projectToSnd(c));
	}

	private Stream<Condition<LETTER, PLACE>> streamNonCutoffCoRelatedConditions(final Condition<LETTER, PLACE> c,
			final Set<Transition<LETTER, PLACE>> transitions) {
		return Stream.concat(c.getPredecessorEvent().getConditionMark().stream(),
				(streamCoRelatedEvents(c, transitions).filter(x -> !x.isCutoffEvent()))
						.flatMap(x -> x.getSuccessorConditions().stream()));
	}

	@Override
	public void update(final Event<LETTER, PLACE> e) {
		if (e.getTransition() == null) {
			// e is out initial dummy event
			assert e.getPredecessorConditions().isEmpty() : "not initial event";
			return;
		}
		// An existing condition c is in co-relation with e if the predecessor event
		// of c is in co-relation with all predecessor events of e.
		// Successor conditions of e are in co-relation with all events e' that are
		// in co-relation with all predecessor conditions of e.
		final Set<Event<LETTER, PLACE>>[] coRelatedEvents = e.getPredecessorConditions().stream()
				.map(x -> streamCoRelatedEvents(x).collect(Collectors.toSet())).toArray(Set[]::new);
		final Set<Event<LETTER, PLACE>> intersection = DataStructureUtils.intersection(Arrays.asList(coRelatedEvents));
		for (final Event<LETTER, PLACE> coRelatedEvent : intersection) {
			for (final Condition<LETTER, PLACE> c : e.getSuccessorConditions()) {
				mCoRelation.addTriple(c, coRelatedEvent.getTransition(), coRelatedEvent);
			}
			for (final Condition<LETTER, PLACE> c : coRelatedEvent.getSuccessorConditions()) {
				mCoRelation.addTriple(c, e.getTransition(), e);
			}
		}
		for (final Condition<LETTER, PLACE> c : e.getConditionMark()) {
			if (!c.getPredecessorEvent().equals(e)) {
				mCoRelation.addTriple(c, e.getTransition(), e);
			}
		}
	}

	@Override
	public boolean isInCoRelation(final Condition<LETTER, PLACE> c1, final Condition<LETTER, PLACE> c2) {
		final boolean result =
				mCoRelation.containsTriple(c1, c2.getPredecessorEvent().getTransition(), c2.getPredecessorEvent())
						|| (c1.getPredecessorEvent().conditionMarkContains(c2));
		assert result == isInCoRelationNaive(c1, c2) : String
				.format("contradictory co-Relation for %s,%s: normal=%b != %b=naive", c1, c2, result, !result);
		if (result) {
			mQueryCounterYes++;
		} else {
			mQueryCounterNo++;
		}
		return result;
	}

	private boolean isInCoRelationNaive(final Condition<LETTER, PLACE> c1, final Condition<LETTER, PLACE> c2) {
		return !mBranchingProcess.inCausalRelation(c1, c2) && !mBranchingProcess.inConflict(c1, c2);
	}

	/**
	 * Checks if two events are in irreflexive co-relation, hereafter "ic".
	 * <p>
	 * x ic y iif (x co y and x != y)
	 * <p>
	 * with *e we denote the predecessor-nodes of e.
	 * <p>
	 * 1. If e1 ic e2 then their parents are pairwise in irreflexive co-relation.<br>
	 * <b>Proof:</b> <br>
	 * let e1 co e2. Furthermore let ci be a predecessor of ei for i \in {1,2}
	 * <p>
	 * If c1#c2 then e1#e2 _|_.<br>
	 * If c1 and c2 are equal then e1#e2 or e1=e2 _|_.<br>
	 * If c1 and c2 are in causal relation, then e1 is in causal relation to e2 or e1 # e2 _|_<br>
	 * q.e.d.
	 * <p>
	 * 2. If for all c1 \in *e1, c2 \in *e2: c1 ic c2 then e1 ci e2.<br>
	 * <b>Proof:</b>Assume the left side of the implication.<br>
	 *
	 * <u>TODO schaetzc 2018-08-16: The next line is not true in the general case. It is possible for a transition/event
	 * to have no predecessors. In a bounded net such transition must also have no successors. Do we support such
	 * transitions?</u><br>
	 *
	 * If e1 = e2 it is trivial, that there are c1,c2 s.t. c1=c2 _|_<br>
	 * Assume e1 < e2, then there has to be a path between e1 and e2 s.t. \exists c1 \in *e1 s.t. c1 < e2. For each
	 * parent c2 \in *e2 then c1 < c2 holds. (e1 > e2 analogously) _|_<br>
	 * Note: This is based on the assumption, that both Events have at least one predecessor-condition. <br>
	 * Assume e1#e2. There is a Condition c and Events e1', e2' \in c* s.t. e1' < e1 and e2' < e2. There is c1 \in *e1
	 * s.t. either c1 < c or c1=c.<br>
	 * If e2 = e2' then c \in *e2 _|_ (e1=e1' analogously). <br>
	 * If e1 != e1' and e2 != e2' then there are predecessor-conditions c1 \in *e1, c2 \in *e2 s.t. c1#c2 _|_. <br>
	 * q.e.d.
	 *
	 * @param e1
	 *            An event
	 * @param e2
	 *            Another event
	 * @return e1 ic e2 (e1 and e2 are in irreflexive co-relation)
	 */
	public boolean isInIrreflexiveCoRelation(final Event<LETTER, PLACE> e1, final Event<LETTER, PLACE> e2) {
		if (e1 == e2) {
			return false;
		}
		if (mBranchingProcess.getDummyRoot() == e1 || mBranchingProcess.getDummyRoot() == e2) {
			return false;
		}
		final Collection<Condition<LETTER, PLACE>> conditions1 = e1.getPredecessorConditions();
		final Collection<Condition<LETTER, PLACE>> conditions2 = e2.getPredecessorConditions();
		for (final Condition<LETTER, PLACE> c1 : conditions1) {
			// e1 and e2 are in conflict
			if (conditions2.contains(c1) || !isCoset(conditions2, c1)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean isInCoRelation(final Condition<LETTER, PLACE> cond, final Event<LETTER, PLACE> event) {
		if (event.getPredecessorConditions().contains(cond)) {
			return false;
		}
		return isCoset(event.getPredecessorConditions(), cond);
	}

	@Override
	public boolean isCoset(final Collection<Condition<LETTER, PLACE>> coSet, final Condition<LETTER, PLACE> c) {
		for (final Condition<LETTER, PLACE> condition : coSet) {
			if (!isInCoRelation(c, condition)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		return mCoRelation.toStringAsTable();
	}

	@Override
	public Set<Condition<LETTER, PLACE>> computeCoRelatatedConditions(final Condition<LETTER, PLACE> cond) {
		final Set<Condition<LETTER, PLACE>> result = streamCoRelatedConditions(cond).collect(Collectors.toSet());
		if (EXTENDED_ASSERTION_CHECKING) {
			assert result
					.equals(computeCoRelatatedConditionsInefficient(cond)) : "inconsistent co-relation information";
		}
		return result;
	}

	@Override
	public Set<Condition<LETTER, PLACE>> computeNonCutoffCoRelatatedConditions(final Condition<LETTER, PLACE> cond) {
		final Set<Condition<LETTER, PLACE>> result =
				streamNonCutoffCoRelatedConditions(cond).collect(Collectors.toSet());
		return result;
	}

	private Set<Condition<LETTER, PLACE>> computeCoRelatatedConditionsInefficient(final Condition<LETTER, PLACE> cond) {
		final Set<Condition<LETTER, PLACE>> result = new HashSet<>();
		for (final Condition<LETTER, PLACE> c2 : mBranchingProcess.getConditions()) {
			if (isInCoRelation(cond, c2)) {
				result.add(c2);
			}
		}
		return result;
	}

	@Override
	public int computeMaximalDegree() {
		final Function<Condition<LETTER, PLACE>, Integer> computeDegree =
				(c -> streamCoRelatedEvents(c).map(e -> e.getSuccessorConditions().size()).reduce(0, Integer::sum));
		final Integer max =
				mCoRelation.projectToFst().stream().map(computeDegree).max(Integer::compare).orElse(Integer.valueOf(0));
		return max;
	}

	@Override
	public Set<Condition<LETTER, PLACE>> computeCoRelatatedConditions(final Condition<LETTER, PLACE> cond,
			final PLACE p) {
		final Set<Transition<LETTER, PLACE>> transitions =
				mBranchingProcess.getYetKnownPredecessorTransitions().getImage(p);
		return streamCoRelatedConditions(cond, transitions).filter(x -> x.getPlace().equals(p))
				.collect(Collectors.toSet());
	}

	@Override
	public Set<Event<LETTER, PLACE>> computeCoRelatatedEvents(final Event<LETTER, PLACE> e) {
		final Set<Condition<LETTER, PLACE>> succCond = e.getSuccessorConditions();
		if (succCond.isEmpty()) {
			throw new UnsupportedOperationException("event without successor conditions");
		}
		final Iterator<Condition<LETTER, PLACE>> it = succCond.iterator();
		final Condition<LETTER, PLACE> firstCond = it.next();
		final Set<Event<LETTER, PLACE>> result = streamCoRelatedEvents(firstCond).collect(Collectors.toSet());
		while (it.hasNext()) {
			final Condition<LETTER, PLACE> c = it.next();
			final Set<Event<LETTER, PLACE>> coRelated = streamCoRelatedEvents(c).collect(Collectors.toSet());
			result.retainAll(coRelated);
		}
		return result;
	}

	@Override
	public Set<Event<LETTER, PLACE>> computeCoRelatatedEvents(final Condition<LETTER, PLACE> c) {
		return streamCoRelatedEvents(c).collect(Collectors.toSet());
	}

}
