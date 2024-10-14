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

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedIteratorNoopConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;
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
	private final Set<ProductPredicate> mAllProductStates = new HashSet<>();
	private static final boolean CHECK_ASSUMPTION_LOCATIONS = true;

	public YamlWitnessProductAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final Witness witness, final PredicateFactory predicateFactory) {
		mAbstraction = abstraction;
		mWitness = witness;
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
	/**
	 * Returns initial ProductPredicates for every initial state of the program automaton and every violation sequence
	 */
	public Iterable<IPredicate> getInitialStates() {
		return () -> new NestedIteratorNoopConstruction<>(mAbstraction.getInitialStates().iterator(), s -> IntStream
				.range(0, mWitness.getEntries().size()).mapToObj(i -> createProductState(s, 0, i)).iterator());
	}

	@Override
	public boolean isInitial(final IPredicate state) {
		final ProductPredicate productState = (ProductPredicate) state;
		return mAbstraction.isInitial(productState.getUnderlying()) && productState.getSegmentCounter() == 0;
	}

	@Override
	public boolean isFinal(final IPredicate state) {
		// A product state is accepting, if the underlying state is accepting, the the witness was fully read, and the
		// previous waypoint was a target.
		final ProductPredicate productState = (ProductPredicate) state;
		if (productState.getSegmentCounter() == 0) {
			// Therefore we cannot accept, if no segment was read.
			return false;
		}
		final ViolationSequence violationSequence =
				(ViolationSequence) mWitness.getEntries().get(productState.getViolationSequenceCounter());
		final Segment previousSegment = violationSequence.getSegments().get(productState.getSegmentCounter() - 1);
		return previousSegment.getFollowWaypoint() instanceof WaypointTarget
				&& mAbstraction.isFinal(productState.getUnderlying())
				&& productState.getSegmentCounter() == violationSequence.getSegments().size();
	}

	@Override
	public int size() {
		return mAllProductStates.size();
	}

	@Override
	public String sizeInformation() {
		return "has currently " + size() + " states, but on-demand construction may add more states";
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, IPredicate>> internalSuccessors(final IPredicate state,
			final LETTER letter) {
		final ProductPredicate productState = (ProductPredicate) state;
		final int successorSegmentCounter = getSuccessorCounter(productState, letter);
		if (successorSegmentCounter == -1) {
			return List.of();
		}
		return () -> new TransformIterator<>(
				mAbstraction.internalSuccessors(productState.getUnderlying(), letter).iterator(),
				x -> new OutgoingInternalTransition<>(letter, createProductState(x.getSucc(), successorSegmentCounter,
						productState.getViolationSequenceCounter())));
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, IPredicate>> callSuccessors(final IPredicate state,
			final LETTER letter) {
		final ProductPredicate productState = (ProductPredicate) state;
		final int successorSegmentCounter = getSuccessorCounter(productState, letter);
		if (successorSegmentCounter == -1) {
			return List.of();
		}
		return () -> new TransformIterator<>(
				mAbstraction.callSuccessors(productState.getUnderlying(), letter).iterator(),
				x -> new OutgoingCallTransition<>(letter, createProductState(x.getSucc(), successorSegmentCounter,
						productState.getViolationSequenceCounter())));
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final LETTER letter) {
		final ProductPredicate productState = (ProductPredicate) state;
		final ProductPredicate productHier = (ProductPredicate) hier;
		final IPredicate currentUnderlying = productState.getUnderlying();
		final int successorSegmentCounter = getSuccessorCounter(productState, letter);
		if (successorSegmentCounter == -1) {
			return List.of();
		}
		return () -> new TransformIterator<>(
				mAbstraction.returnSuccessors(currentUnderlying, productHier.getUnderlying(), letter).iterator(),
				x -> new OutgoingReturnTransition<>(productHier, letter, createProductState(x.getSucc(),
						successorSegmentCounter, productState.getViolationSequenceCounter())));
	}

	/** returns the appropriate segment counter for the successors of the product state and letter */
	private int getSuccessorCounter(final ProductPredicate productState, final LETTER letter) {
		final List<Segment> segments =
				((ViolationSequence) mWitness.getEntries().get(productState.getViolationSequenceCounter()))
						.getSegments();
		for (int sCounter = productState.getSegmentCounter(); sCounter < segments.size(); sCounter++) {
			final Segment currentSegment = segments.get(sCounter);
			// check if an Avoid Waypoint of the segment matches (Assumption Waypoints are ignored)
			if (currentSegment.getAvoidWaypoints().stream().anyMatch(x -> matchesWaypoint(letter, x))) {
				return -1;
			}
			final Waypoint currentFollowWaypoint = currentSegment.getFollowWaypoint();
			// check follow assumption waypoints separately because they can match simultaneously with other waypoints
			if (currentFollowWaypoint instanceof WaypointAssumption
					&& (!CHECK_ASSUMPTION_LOCATIONS || matchesStartLocation(letter, currentFollowWaypoint))) {
				continue;
			}
			return matchesWaypoint(letter, currentFollowWaypoint) ? sCounter + 1 : sCounter;
		}
		return segments.size();
	}

	/** Checks if the waypoint matches with the statement. Assumption waypoints are not matched */
	private boolean matchesWaypoint(final LETTER statement, final Waypoint waypoint) {
		if (waypoint instanceof WaypointBranching && matchesStartLocation(statement, waypoint)) {
			final ConditionAnnotation conditionAnnot = ConditionAnnotation.getAnnotation(statement);
			return conditionAnnot != null
					&& Boolean.parseBoolean(waypoint.getConstraint()) == !conditionAnnot.isNegated();
		}
		if (waypoint instanceof WaypointTarget) {
			return matchesStartLocation(statement, waypoint);
		}
		if (waypoint instanceof WaypointFunctionEnter) {
			return matchesEndLocation(statement, waypoint);
		}
		if (waypoint instanceof WaypointFunctionReturn) {
			if (statement instanceof IIcfgReturnTransition) {
				// function_return waypoints match the location of the function call
				return matchesEndLocation(((IIcfgReturnTransition<?, ?>) statement).getCorrespondingCall(), waypoint);
			}
			return matchesEndLocation(statement, waypoint);
		}
		return false;
	}

	/** Returns true if the start line and column of the statement match the location of the waypoint */
	private static boolean matchesStartLocation(final IElement statement, final Waypoint waypoint) {
		final ILocation programLoc = ILocation.getAnnotation(statement);
		final Location witnessLoc = waypoint.getLocation();
		return programLoc.getStartLine() == witnessLoc.getLine()
				&& (witnessLoc.getColumn() == null || witnessLoc.getColumn() == programLoc.getStartColumn());
	}

	/** Returns true if the end line and column of the statement match the location of the waypoint */
	private static boolean matchesEndLocation(final IElement statement, final Waypoint waypoint) {
		final ILocation programLoc = ILocation.getAnnotation(statement);
		final Location witnessLoc = waypoint.getLocation();
		return programLoc.getEndLine() == witnessLoc.getLine()
				&& (witnessLoc.getColumn() == null || witnessLoc.getColumn() == programLoc.getEndColumn());
	}

	/** Creates a ProductPredicate with the counters */
	private IPredicate createProductState(final IPredicate predicate, final int waypointCounter,
			final int violationSequenceCounter) {
		final ProductPredicate result =
				new ProductPredicate((ISLPredicate) predicate, waypointCounter, violationSequenceCounter);
		mAllProductStates.add(result);
		return result;
	}

	/**
	 * IPredicate annotated with counters for the Violation Sequence and Segments of an entry-based violation witness
	 */
	private static final class ProductPredicate extends AnnotatedPredicate<ISLPredicate, Pair<Integer, Integer>>
			implements ISLPredicate {
		public ProductPredicate(final ISLPredicate underlying, final int segmentCounter,
				final int violationSequenceCounter) {
			super(underlying, new Pair<>(segmentCounter, violationSequenceCounter));
		}

		public int getSegmentCounter() {
			return mAnnotation.getFirst();

		}

		public int getViolationSequenceCounter() {
			return mAnnotation.getSecond();
		}

		@Override
		public IcfgLocation getProgramPoint() {
			return mUnderlying.getProgramPoint();
		}
	}
}
