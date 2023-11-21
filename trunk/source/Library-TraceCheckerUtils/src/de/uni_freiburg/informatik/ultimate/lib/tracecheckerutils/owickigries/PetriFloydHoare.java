/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Constructs an Floyd-Hoare annotation of a Petri program from a branching process of the final refined Petri Net.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <P>
 *            The type of places in the Petri program
 * @param <L>
 *            The type of statements in the Petri program
 */
public class PetriFloydHoare<P extends IPredicate, L> {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mFactory;
	private final List<IPredicateUnifier> mPredicateUnifiers;

	private final boolean mCoveringSimplification;

	private final IPetriNet<L, P> mOriginalProgram;
	private final Set<Marking<P>> mOriginalReach;
	private final Set<P> mOriginalPlaces;

	private final BranchingProcess<L, P> mRefinedUnfolding;
	private final Set<Marking<P>> mRefinedReach;
	private final Set<P> mAssertionPlaces;

	private final Map<Marking<P>, IPredicate> mFloydHoareAnnotation;

	public PetriFloydHoare(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final BranchingProcess<L, P> bp, final IPetriNet<L, P> net, final List<IPredicateUnifier> predicateUnifiers,
			final boolean iterativeCosets, final boolean coveringSimplification) {
		this(services, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), bp, net, predicateUnifiers,
				iterativeCosets, coveringSimplification);
	}

	public PetriFloydHoare(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final BranchingProcess<L, P> bp, final IPetriNet<L, P> net,
			final List<IPredicateUnifier> predicateUnifiers, final boolean iterativeCosets,
			final boolean coveringSimplification) {
		mServices = services;
		mManagedScript = mgdScript;
		mPredicateUnifiers = predicateUnifiers;
		mFactory = new BasicPredicateFactory(mServices, mManagedScript, symbolTable);

		mOriginalProgram = net;
		mRefinedUnfolding = bp;

		final var refinedReachablePlaces =
				mRefinedUnfolding.getConditions().stream().map(Condition::getPlace).collect(Collectors.toSet());
		mOriginalPlaces = Collections.unmodifiableSet(mOriginalProgram.getPlaces());
		mAssertionPlaces = DataStructureUtils.difference(refinedReachablePlaces, mOriginalPlaces);

		mRefinedReach = computeReachableMarkings(mRefinedUnfolding);
		mOriginalReach = mRefinedReach.stream().map(this::projectToOriginal).collect(Collectors.toSet());

		mCoveringSimplification = coveringSimplification;
		if (iterativeCosets) {
			mFloydHoareAnnotation = getCosetAnnotation();
		} else {
			mFloydHoareAnnotation = getMaximalAnnotation();
		}
	}

	// computes the reachable markings of the refined net
	private static <L, P> Set<Marking<P>> computeReachableMarkings(final BranchingProcess<L, P> bp) {
		return bp.getEvents().stream()
				// small optimization, cut-off event has same condition mark as companion
				// .filter(e -> !e.isCutoffEvent())
				.map(Event::getMark).collect(Collectors.toSet());
	}

	// ------------------
	// maximal annotation
	// ------------------

	/**
	 * Annotation with MaximalCosets computation
	 */
	private Map<Marking<P>, IPredicate> getMaximalAnnotation() {
		return mOriginalReach.stream().collect(Collectors.toMap(Function.identity(), this::getMarkingAssertion));
	}

	private IPredicate getMarkingAssertion(final Marking<P> originalMarking) {
		final Set<IPredicate> disjuncts = new HashSet<>();
		for (final Marking<P> refinedMarking : getRefinedMarkingsForOriginal(originalMarking)) {
			disjuncts.add(mFactory.and(getAssertPlaces(refinedMarking)));
		}
		return mFactory.or(disjuncts);
	}

	private Marking<P> projectToOriginal(final Marking<P> refinedMarking) {
		return new Marking<>(
				refinedMarking.stream().filter(mOriginalPlaces::contains).collect(ImmutableSet.collector()));
	}

	private Set<Marking<P>> getRefinedMarkingsForOriginal(final Marking<P> originalMarking) {
		return mRefinedReach.stream().filter(m -> originalMarking.equals(projectToOriginal(m)))
				.collect(Collectors.toSet());
	}

	private Set<? extends IPredicate> getAssertPlaces(final Marking<P> refinedMarking) {
		final var assertPlaces = DataStructureUtils.intersection(refinedMarking.getPlaces(), mAssertionPlaces);
		if (mCoveringSimplification) {
			return simplifyAssertions((Set) assertPlaces);
		}
		return assertPlaces;
	}

	// ---------------------------
	// Iterative co-set annotation
	// ---------------------------

	/**
	 * Cuts computation from "greedy" algorithm With simplification
	 */
	private Map<Marking<P>, IPredicate> getCosetAnnotation() {
		final var originalConditions = getOriginalConditions();
		final var assertionConditions =
				DataStructureUtils.difference(Set.copyOf(mRefinedUnfolding.getConditions()), originalConditions);

		final Map<Marking<P>, IPredicate> mapping = new HashMap<>();

		// compute maximal co-sets consisting only of original conditions
		// Note: these are not cuts of the unfolding, as there might be co-related assertion conditions.
		final Set<Set<Condition<L, P>>> markingCosets = collectCoSets(Collections.emptySet(), originalConditions);

		for (final Set<Condition<L, P>> markCoset : markingCosets) {
			final Set<Set<Condition<L, P>>> assertConds = collectCoSets(markCoset, assertionConditions);
			final Set<Set<IPredicate>> markAssertPlaces = new HashSet<>();
			for (final Set<Condition<L, P>> assertCond : assertConds) {
				Set<IPredicate> cosetPredicates = getCosetPredicates(assertCond);
				if (mCoveringSimplification) {
					cosetPredicates = simplifyAssertions(cosetPredicates);
				}
				markAssertPlaces.add(cosetPredicates);
			}
			mapping.put(toMarking(markCoset), getMarkingAssertion(markAssertPlaces));
		}
		return mapping;
	}

	private Marking<P> toMarking(final Set<Condition<L, P>> coset) {
		return new Marking<>(coset.stream().map(Condition::getPlace).collect(ImmutableSet.collector()));
	}

	private Set<IPredicate> getCosetPredicates(final Set<Condition<L, P>> coset) {
		return coset.stream().map(Condition::getPlace).collect(Collectors.toSet());
	}

	private Set<Set<Condition<L, P>>> collectCoSets(final Set<Condition<L, P>> compCoset,
			final Set<Condition<L, P>> conditions) {
		final var result = new HashSet<Set<Condition<L, P>>>();
		collectCoSets(Collections.emptySet(), compCoset, conditions, result);
		return result;
	}

	/**
	 * @param coSet
	 * @param conditions
	 * @param maximalCoSets
	 * @return The set of all cosets which are supersets of the given coset, only contain the given conditions, and are
	 *         maximal wrt these constraints
	 */
	private void collectCoSets(final Set<Condition<L, P>> coSet, final Set<Condition<L, P>> compCoset,
			final Set<Condition<L, P>> conditions, final Set<Set<Condition<L, P>>> maximalCoSets) {
		final Set<Set<Condition<L, P>>> largerCoSets = new HashSet<>();

		final Set<Condition<L, P>> remainingConditions = DataStructureUtils.difference(conditions, coSet);
		for (final Condition<L, P> cond : remainingConditions) {
			if (mRefinedUnfolding.getCoRelation().isCoset(compCoset, cond)
					&& mRefinedUnfolding.getCoRelation().isCoset(coSet, cond)) {
				final var enlargedCoSet = DataStructureUtils.union(coSet, DataStructureUtils.toSet(cond));
				largerCoSets.add(enlargedCoSet);
			}
		}

		if (largerCoSets.isEmpty()) {
			// the coSet is already maximal
			maximalCoSets.add(coSet);
		} else {
			for (final Set<Condition<L, P>> largerCoSet : largerCoSets) {
				collectCoSets(largerCoSet, compCoset, remainingConditions, maximalCoSets);
			}
		}
	}

	private Set<Condition<L, P>> getOriginalConditions() {
		return mRefinedUnfolding.getConditions().stream().filter(cond -> mOriginalPlaces.contains(cond.getPlace()))
				.collect(Collectors.toSet());
	}

	// Call this for simple and "greedy" cuts Annotation
	private IPredicate getMarkingAssertion(final Set<Set<IPredicate>> predicatesForCuts) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final var predicatesForCut : predicatesForCuts) {
			predicates.add(getCutAssertion(predicatesForCut));
		}
		return mFactory.or(predicates);
	}

	// phi(d) = conjunction(assert(p)) for each p in z(d) (assertion places) -> Cut assertion
	private IPredicate getCutAssertion(final Set<IPredicate> predicatesForCut) {
		var predicates = predicatesForCut;
		if (mCoveringSimplification) {
			predicates = simplifyAssertions(predicates);
		}
		return mFactory.and(predicates);
	}

	// ------------------------
	// assertion simplification
	// ------------------------

	// Set of conditions to set of places
	private Set<IPredicate> simplifyAssertions(final Set<IPredicate> assertions) {
		Set<IPredicate> simpleAssertions = assertions;
		// Check if equiv to false, set all to false;
		for (final IPredicate cond : assertions) {
			if (!thereIsStronger(cond, simpleAssertions)) {
				final Set<IPredicate> weakerConditions = getWeakerConditions(cond, assertions);
				simpleAssertions = cleanWeakConditions(simpleAssertions, weakerConditions);
			} else {
				simpleAssertions = DataStructureUtils.difference(simpleAssertions, Collections.singleton(cond));
			}
		}
		return simpleAssertions;
	}

	private Set<IPredicate> getWeakerConditions(final IPredicate condition, Set<IPredicate> assertConditions) {
		final Set<IPredicate> condImplications = new HashSet<>();
		assertConditions = DataStructureUtils.difference(assertConditions, Collections.singleton(condition));
		for (final var predUnifier : mPredicateUnifiers) {
			condImplications.addAll(DataStructureUtils.intersection(assertConditions,
					predUnifier.getCoverageRelation().getCoveringPredicates(condition)));
		}
		return condImplications;
	}

	private static Set<IPredicate> cleanWeakConditions(Set<IPredicate> assertConditions,
			final Set<IPredicate> condImplications) {
		if (!condImplications.isEmpty()) {
			assertConditions = DataStructureUtils.difference(assertConditions, condImplications);
		}
		return assertConditions;
	}

	private boolean thereIsStronger(final IPredicate condition, final Set<IPredicate> assertConditions) {
		final Set<IPredicate> assertPredicates =
				DataStructureUtils.difference(assertConditions, Collections.singleton(condition));
		for (final var predUnifier : mPredicateUnifiers) {
			final Set<IPredicate> coveredPlaces = predUnifier.getCoverageRelation().getCoveredPredicates(condition);
			if (DataStructureUtils.haveNonEmptyIntersection(coveredPlaces, assertPredicates)) {
				return true;
			}
		}
		return false;
	}

	// --------------
	// output methods
	// --------------

	public Map<Marking<P>, IPredicate> getResult() {
		return mFloydHoareAnnotation;
	}

	public IPredicate getAssertion(final Marking<P> marking) {
		return mFloydHoareAnnotation.get(marking);
	}
}
