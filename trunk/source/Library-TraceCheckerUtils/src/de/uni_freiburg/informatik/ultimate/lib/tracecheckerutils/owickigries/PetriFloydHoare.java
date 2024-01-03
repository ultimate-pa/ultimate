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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Constructs an Floyd-Hoare annotation of a Petri program from the final refined Petri net.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <L>
 *            The type of statements in the Petri program
 * @param <P>
 *            The type of places in the Petri program
 */
public class PetriFloydHoare<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mFactory;
	private final Function<P, IPredicate> mAssertionPlaceAnnotation;
	// TODO should only be a single relation
	private final List<IPredicateCoverageChecker> mCoverageRelations;

	private final boolean mCoveringSimplification;

	private final IPetriNet<L, P> mOriginalProgram;
	private final IPetriNet<L, P> mRefinedNet;

	private final Set<P> mOriginalPlaces;

	private final Map<Marking<P>, IPredicate> mFloydHoareAnnotation;

	public PetriFloydHoare(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit, final IPetriNet<L, P> refinedNet,
			final Function<P, IPredicate> assertionPlaceAnnotation,
			final List<IPredicateCoverageChecker> coverageRelations, final boolean coveringSimplification) {
		this(services, csToolkit.getManagedScript(), program, csToolkit.getSymbolTable(), refinedNet,
				assertionPlaceAnnotation, coverageRelations, coveringSimplification);
	}

	public PetriFloydHoare(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IPetriNet<L, P> program, final IIcfgSymbolTable symbolTable, final IPetriNet<L, P> refinedNet,
			final Function<P, IPredicate> assertionPlaceAnnotation,
			final List<IPredicateCoverageChecker> coverageRelations, final boolean coveringSimplification) {
		mServices = services;
		mManagedScript = mgdScript;
		mAssertionPlaceAnnotation = assertionPlaceAnnotation;
		mCoverageRelations = coverageRelations;
		mFactory = new BasicPredicateFactory(mServices, mManagedScript, symbolTable);

		mOriginalProgram = program;
		mRefinedNet = refinedNet;

		mOriginalPlaces = Collections.unmodifiableSet(mOriginalProgram.getPlaces());

		final var refinedReach = computeReachableMarkings();
		final var originalToRefined = projectReachableMarkings(refinedReach);

		mCoveringSimplification = coveringSimplification;
		mFloydHoareAnnotation = getMaximalAnnotation(originalToRefined);
	}

	public Map<Marking<P>, IPredicate> getResult() {
		return mFloydHoareAnnotation;
	}

	private Map<Marking<P>, List<Marking<P>>> projectReachableMarkings(final Collection<Marking<P>> refinedReach) {
		final var result = new HashMap<Marking<P>, List<Marking<P>>>();
		for (final var refinedMark : refinedReach) {
			final var original = projectToOriginal(refinedMark);
			result.computeIfAbsent(original, x -> new ArrayList<>()).add(refinedMark);
		}
		return result;
	}

	// a depth-first search of the reachability graph
	private Collection<Marking<P>> computeReachableMarkings() {
		final var net = mRefinedNet;

		final var result = new LinkedHashSet<Marking<P>>();
		final var worklist = new ArrayDeque<Marking<P>>();

		final var initialMarking = new Marking<>(ImmutableSet.of(net.getInitialPlaces()));
		worklist.push(initialMarking);

		while (!worklist.isEmpty()) {
			final var marking = worklist.pop();
			if (!result.add(marking)) {
				continue;
			}

			final var places = marking.getPlaces();
			for (final var transitionProvider : net.getSuccessorTransitionProviders(places, places)) {
				for (final var transition : transitionProvider.getTransitions()) {
					assert marking.isTransitionEnabled(transition);
					try {
						final Marking<P> successor = marking.fireTransition(transition);
						worklist.add(successor);
					} catch (final PetriNetNot1SafeException e) {
						throw new AssertionError("Petri net must be 1-safe", e);
					}
				}
			}
		}

		return result;
	}

	private Map<Marking<P>, IPredicate>
			getMaximalAnnotation(final Map<Marking<P>, List<Marking<P>>> originalToRefined) {
		return originalToRefined.entrySet().stream()
				.collect(Collectors.toMap(Map.Entry::getKey, e -> getMarkingAssertion(e.getValue())));
	}

	private IPredicate getMarkingAssertion(final List<Marking<P>> refinedMarkings) {
		final Set<IPredicate> disjuncts = new HashSet<>();
		for (final Marking<P> refinedMarking : refinedMarkings) {
			disjuncts.add(mFactory.and(getAssertions(refinedMarking)));
		}
		return mFactory.or(disjuncts);
	}

	private Marking<P> projectToOriginal(final Marking<P> refinedMarking) {
		return new Marking<>(
				refinedMarking.stream().filter(mOriginalPlaces::contains).collect(ImmutableSet.collector()));
	}

	private Set<IPredicate> getAssertions(final Marking<P> refinedMarking) {
		final var assertPlaces = DataStructureUtils.difference(refinedMarking.getPlaces(), mOriginalPlaces);
		final var assertions = assertPlaces.stream().map(mAssertionPlaceAnnotation).collect(Collectors.toSet());
		if (mCoveringSimplification) {
			return simplifyAssertions(assertions);
		}
		return assertions;
	}

	// ------------------------
	// assertion simplification
	// ------------------------

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
		for (final var coverage : mCoverageRelations) {
			condImplications.addAll(
					DataStructureUtils.intersection(assertConditions, coverage.getCoveringPredicates(condition)));
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
		for (final var coverage : mCoverageRelations) {
			final Set<IPredicate> coveredPlaces = coverage.getCoveredPredicates(condition);
			if (DataStructureUtils.haveNonEmptyIntersection(coveredPlaces, assertPredicates)) {
				return true;
			}
		}
		return false;
	}
}
