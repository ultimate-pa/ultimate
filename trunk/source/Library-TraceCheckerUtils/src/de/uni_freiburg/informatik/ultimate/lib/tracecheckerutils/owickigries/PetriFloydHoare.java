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

	private final BranchingProcess<L, P> mRefinedUnfolding;
	private final Set<Condition<L, P>> mOriginalConditions;
	private final Set<Condition<L, P>> mAssertionConditions;

	private final Set<Marking<P>> mRefinedReach;
	private final Set<P> mAssertionPlaces;

	private final IPetriNet<L, P> mOriginalProgram;
	private final Set<Marking<P>> mOriginalReach;
	private final Set<P> mOriginalPlaces;

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
		mRefinedReach = computeReachableMarkings(mRefinedUnfolding);

		mOriginalPlaces = Collections.unmodifiableSet(mOriginalProgram.getPlaces());
		mOriginalConditions = getOriginalConditions();
		mAssertionConditions =
				DataStructureUtils.difference(Set.copyOf(mRefinedUnfolding.getConditions()), mOriginalConditions);

		mAssertionPlaces = DataStructureUtils.difference(refinedReachablePlaces, mOriginalPlaces);
		mOriginalReach = mRefinedReach.stream().map(this::projectToOriginal).collect(Collectors.toSet());

		if (iterativeCosets) {
			mFloydHoareAnnotation = getCosetAnnotation();
		} else {
			mFloydHoareAnnotation = getMaximalAnnotation();
		}
		mCoveringSimplification = coveringSimplification;

	}

	// computes the reachable markings of the refined net
	private static <L, P> Set<Marking<P>> computeReachableMarkings(final BranchingProcess<L, P> bp) {
		return bp.getEvents().stream()
				// small optimization, cut-off event has same condition mark as companion
				// .filter(e -> !e.isCutoffEvent())
				.map(Event::getMark).collect(Collectors.toSet());
	}

	/**
	 * Annotation with MaximalCosets computation
	 */
	private Map<Marking<P>, IPredicate> getMaximalAnnotation() {
		final Map<Marking<P>, IPredicate> mapping = new HashMap<>();
		for (final Marking<P> marking : mOriginalReach) {
			mapping.put(marking, getMarkingAssertion(marking));
		}
		return mapping;
	}

	/**
	 * Cuts computation from "greedy" algorithm With simplification
	 */
	private Map<Marking<P>, IPredicate> getCosetAnnotation() {
		final Map<Marking<P>, IPredicate> mapping = new HashMap<>();
		final Set<Set<Condition<L, P>>> markingCosets = getCosets(new HashSet<Condition<L, P>>(),
				new HashSet<Condition<L, P>>(), mOriginalConditions, new HashSet<Set<Condition<L, P>>>());
		for (final Set<Condition<L, P>> markCoset : markingCosets) {
			final ImmutableSet<P> markPlaces = getCosetPlaces(markCoset);
			final Set<Set<Condition<L, P>>> assertConds = getCosets(new HashSet<Condition<L, P>>(), markCoset,
					mAssertionConditions, new HashSet<Set<Condition<L, P>>>());
			final Set<Set<IPredicate>> markAssertPlaces = new HashSet<>();
			for (final Set<Condition<L, P>> assertCond : assertConds) {
				Set<IPredicate> cosetPredicates = getCosetPredicates(assertCond);
				if (mCoveringSimplification) {
					cosetPredicates = simplifyAssertions(cosetPredicates);
				}
				markAssertPlaces.add(cosetPredicates);
			}
			mapping.put(new Marking<>(markPlaces), getMarkingAssertion(markPlaces, markAssertPlaces));
		}
		return mapping;
	}

	private ImmutableSet<P> getCosetPlaces(final Set<Condition<L, P>> coset) {
		return coset.stream().map(Condition::getPlace).collect(ImmutableSet.collector());
	}

	private Set<IPredicate> getCosetPredicates(final Set<Condition<L, P>> coset) {
		return coset.stream().map(Condition::getPlace).collect(Collectors.toSet());
	}

	// Set of conditions to set of places
	private Set<IPredicate> simplifyAssertions(final Set<IPredicate> assertConds) {
		Set<IPredicate> simpleAssertions = assertConds;
		// Check if equiv to false, set all to false;
		for (final IPredicate cond : assertConds) {
			if (!thereIsStronger(cond, simpleAssertions)) {
				final Set<IPredicate> weakerConditions = getWeakerConditions(cond, assertConds);
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
			if (!DataStructureUtils.intersection(coveredPlaces, assertPredicates).isEmpty()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param coset
	 * @param conditions
	 * @param cuts
	 * @return set successor maximal cosets from given coset
	 */
	private Set<Set<Condition<L, P>>> getCosets(final Set<Condition<L, P>> coset, final Set<Condition<L, P>> compCoset,
			final Set<Condition<L, P>> conditions, Set<Set<Condition<L, P>>> cuts) {
		final Set<Condition<L, P>> toAdd = DataStructureUtils.difference(conditions, coset);
		final Set<Set<Condition<L, P>>> cosets = new HashSet<>();
		for (final Condition<L, P> cond : toAdd) {
			if (mRefinedUnfolding.getCoRelation().isCoset(compCoset, cond)
					& mRefinedUnfolding.getCoRelation().isCoset(coset, cond)) {
				final Set<Condition<L, P>> imCoset = DataStructureUtils.union(coset, DataStructureUtils.toSet(cond));
				cosets.add(imCoset);
			}
		}
		if (!cosets.isEmpty()) {
			for (final Set<Condition<L, P>> imcoset : cosets) {
				cuts = DataStructureUtils.union(cuts, getCosets(imcoset, compCoset, conditions, cuts));
			}
		} else {
			cuts.add(coset);
		}
		return cuts;
	}

	private Set<Condition<L, P>> getOriginalConditions() {
		return mRefinedUnfolding.getConditions().stream().filter(cond -> mOriginalPlaces.contains(cond.getPlace()))
				.collect(Collectors.toSet());
	}

	private IPredicate getMarkingAssertion(final Marking<P> originalMarking) {
		final Set<IPredicate> disjuncts = new HashSet<>();
		for (final Marking<P> refinedMarking : getRefinedMarkingsForOriginal(originalMarking)) {
			disjuncts.add(mFactory.and(getAssertPlaces(refinedMarking)));
		}
		return mFactory.or(disjuncts);
	}

	// Call this for simple and "greedy" cuts Annotation
	private IPredicate getMarkingAssertion(final Set<P> marking, final Set<Set<IPredicate>> cuts) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final Set<IPredicate> cut : cuts) {
			predicates.add(getCutAssertion(cut));
		}
		return mFactory.or(predicates);
	}

	// phi(d) = conjunction(assert(p)) for each p in z(d) (assertion places) -> Cut assertion
	private IPredicate getCutAssertion(final Set<IPredicate> cut) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final IPredicate place : cut) {
			predicates.add(place);
		}
		return mFactory.and(predicates);
	}

	private Marking<P> projectToOriginal(final Marking<P> cut) {
		return new Marking<>(cut.stream().filter(mOriginalPlaces::contains).collect(ImmutableSet.collector()));
	}

	private Set<Marking<P>> getRefinedMarkingsForOriginal(final Marking<P> originalMarking) {
		return mRefinedReach.stream().filter(m -> originalMarking.equals(projectToOriginal(m)))
				.collect(Collectors.toSet());
	}

	private Set<P> getAssertPlaces(final Marking<P> refinedMarking) {
		return DataStructureUtils.intersection(refinedMarking.getPlaces(), mAssertionPlaces);
	}

	// output methods
	// --------------

	public Map<Marking<P>, IPredicate> getResult() {
		return mFloydHoareAnnotation;
	}

	public IPredicate getAssertion(final Marking<P> marking) {
		return mFloydHoareAnnotation.get(marking);
	}
}
