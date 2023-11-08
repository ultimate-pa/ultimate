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
import java.util.LinkedHashSet;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Constructs an Floyd-Hoare annotation from a branching process of the final refined Petri Net.
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
	private final DefaultIcfgSymbolTable mSymbolTable;
	private final BasicPredicateFactory mFactory;
	private final List<IPredicateUnifier> mPredicateUnifiers;
	private final boolean mCoveringSimplification;

	private final BranchingProcess<L, P> mBp;

	private final Set<Condition<L, P>> mConditions;
	private final Set<Condition<L, P>> mOriginalConditions;
	private final Set<Condition<L, P>> mAssertionConditions;
	private final Set<ImmutableSet<P>> mCuts;

	private final IPetriNet<L, P> mNet;

	private final Set<P> mPlaces;
	private final Set<P> mOriginalPlaces;
	private final Set<P> mAssertionPlaces;
	private final Set<ImmutableSet<P>> mReach;

	private final Map<Marking<P>, IPredicate> mFloydHoareAnnotation;

	public PetriFloydHoare(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final BranchingProcess<L, P> bp, final IPetriNet<L, P> net, final List<IPredicateUnifier> predicateUnifiers,
			final boolean iterativeCosets, final boolean coveringSimplification) {
		this(services, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(), bp, net,
				predicateUnifiers, iterativeCosets, coveringSimplification);
	}

	/**
	 * @TODO: assertion, places are IPredicate
	 * @param services
	 * @param csToolkit
	 * @param bp
	 * @param assertion
	 */
	public PetriFloydHoare(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final Set<String> procedures, final BranchingProcess<L, P> bp,
			final IPetriNet<L, P> net, final List<IPredicateUnifier> predicateUnifiers, final boolean iterativeCosets,
			final boolean coveringSimplification) {
		mServices = services;
		mManagedScript = mgdScript;
		mSymbolTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		mFactory = new BasicPredicateFactory(mServices, mManagedScript, mSymbolTable);
		mPredicateUnifiers = predicateUnifiers;

		mBp = bp;
		mNet = net;

		mCuts = computeMaximalCosets(mBp);

		mOriginalPlaces = new HashSet<>(mNet.getPlaces());
		mConditions = mBp.getConditions().stream().collect(Collectors.toSet());
		mOriginalConditions = getOrigConditions();
		mAssertionConditions = DataStructureUtils.difference(mConditions, mOriginalConditions);

		mPlaces = getPlaces(mCuts);
		mAssertionPlaces = getAssertPlaces(mPlaces, mOriginalPlaces);
		mReach = getReach(mCuts);

		if (iterativeCosets) {
			mFloydHoareAnnotation = getCosetAnnotation();
		} else {
			mFloydHoareAnnotation = getMaximalAnnotation();
		}
		mCoveringSimplification = coveringSimplification;

	}

	// public static <LETTER> OwickiGriesFloydHoare<IPredicate, LETTER> create(final IUltimateServiceProvider services,
	// final CfgSmtToolkit csToolkit, final BranchingProcess<LETTER, IPredicate> bp,
	// final IPetriNet<LETTER, IPredicate> net,
	// ArrayList <IRefinementEngine<LETTER, NestedWordAutomaton<LETTER, IPredicate>>> refinementEngines) {
	// return new OwickiGriesFloydHoare<>(services, csToolkit, bp, net, x -> x, refinementEngines);
	// }

	/**
	 * @param branching
	 *            process
	 * @return set of all maximal co-set (cuts)
	 */
	private static <LETTER, PLACE> Set<ImmutableSet<PLACE>>
			computeMaximalCosets(final BranchingProcess<LETTER, PLACE> bp) {
		final Set<ImmutableSet<PLACE>> maximalCoSets = new LinkedHashSet<>();
		for (final Event<LETTER, PLACE> event : bp.getEvents()) {
			// small optimization, cut-off event has same condition mark as companion
			// if (!event.isCutoffEvent()) {
			maximalCoSets.add(event.getMark().stream().collect(ImmutableSet.collector()));
			// }
		}
		return maximalCoSets;
	}

	/**
	 * Annotation with MaximalCosets computation
	 */
	private Map<Marking<P>, IPredicate> getMaximalAnnotation() {
		final Map<Marking<P>, IPredicate> mapping = new HashMap<>();
		for (final ImmutableSet<P> marking : mReach) {
			mapping.put(new Marking<>(marking), getMarkingAssertion(marking));
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
		final Set<P> placeCoset = new HashSet<>();
		for (final Condition<L, P> condition : coset) {
			placeCoset.add(condition.getPlace());
		}
		return ImmutableSet.of(placeCoset);

	}

	private Set<IPredicate> getCosetPredicates(final Set<Condition<L, P>> coset) {
		final Set<IPredicate> predCoset = new HashSet<>();
		for (final Condition<L, P> condition : coset) {
			predCoset.add(condition.getPlace());
		}
		return predCoset;

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

	private Set<IPredicate> cleanWeakConditions(Set<IPredicate> assertConditions,
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
			if (mBp.getCoRelation().isCoset(compCoset, cond) & mBp.getCoRelation().isCoset(coset, cond)) {
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

	private Set<Condition<L, P>> getOrigConditions() {
		final Set<Condition<L, P>> conditions = new HashSet<>();
		for (final Condition<L, P> cond : mBp.getConditions()) {
			if (mOriginalPlaces.contains(cond.getPlace())) {
				conditions.add(cond);
			}
		}
		return conditions;
	}

	private IPredicate getMarkingAssertion(final Set<P> marking) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final Set<P> cut : getCuts(marking)) {
			predicates.add(getCutAssertion(cut, getAssertPlaces(cut)));
		}
		return mFactory.or(predicates);
	}

	private IPredicate getCutAssertion(final Set<P> cut, final Set<P> assertPlaces) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final IPredicate place : assertPlaces) {
			predicates.add(place);
		}
		return mFactory.and(predicates);
	}

	// Call this for simple and "greedy" cuts Annotation
	private IPredicate getMarkingAssertion(final Set<P> marking, final Set<Set<IPredicate>> cuts) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final Set<IPredicate> cut : cuts) {
			predicates.add(getCutAssertion(cut));
		}
		return mFactory.or(predicates);
	}

	// phi(d) = conjuct(assert(p)) for each p in z(d) (assertion places) -> Cut assertion
	private IPredicate getCutAssertion(final Set<IPredicate> cut) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final IPredicate place : cut) {
			predicates.add(place);
		}
		return mFactory.and(predicates);
	}

	/**
	 * @param cuts
	 * @return set of all places in Petri Net* TODO: or get it as parameter from Net.getPlaces()
	 */
	private Set<P> getPlaces(final Set<ImmutableSet<P>> cuts) {
		final Set<P> places = new HashSet<>();
		for (final Set<P> cut : cuts) {
			places.addAll(cut);
		}
		return places;
	}

	/**
	 * @param places
	 * @param assertPlaces
	 * @return set of original places
	 * @TODO: remove p_block? Is in any cut? No, right?
	 * @TODO: with Parameters or not?
	 * @TODO: Get original places from Petri Net?
	 */
	private Set<P> getAssertPlaces(final Set<P> places, final Set<P> origPlaces) {
		return DataStructureUtils.difference(places, origPlaces);
	}

	/**
	 * @param cut
	 * @return mark, set of original places in cut
	 */
	private ImmutableSet<P> getCutMarking(final Set<P> cut) {
		final Set<P> mark = new HashSet<>();
		for (final P place : cut) {
			if (mOriginalPlaces.contains(place)) {
				mark.add(place);
			}
		}
		return ImmutableSet.of(mark);
	}

	/**
	 * @param cut
	 * @return set of all assertion places in cut
	 */
	private Set<P> getAssertPlaces(final Set<P> cut) {
		final Set<P> places = new HashSet<>();
		for (final P place : cut) {
			if (mAssertionPlaces.contains(place)) {
				places.add(place);
			}
		}
		return places;
	}

	/**
	 * @param Cuts
	 * @return set of all markings (set of original places)
	 * @TODO: Set<Marking<LETTER, PLACE>> or Set<Set<PLACE>>?
	 */
	private Set<ImmutableSet<P>> getReach(final Set<ImmutableSet<P>> Cuts) {
		final Set<ImmutableSet<P>> markings = new HashSet<>();
		for (final ImmutableSet<P> cut : Cuts) {
			markings.add(getCutMarking(cut));
		}
		return markings;
	}

	/**
	 * @param marking
	 * @return set of cuts that have marking as original marking
	 */
	private Set<Set<P>> getCuts(final Set<P> marking) {
		final Set<Set<P>> cuts = new HashSet<>();
		for (final Set<P> cut : mCuts) {
			if (marking.equals(getCutMarking(cut))) {
				cuts.add(cut);
			}
		}
		return cuts;
	}

	public Map<Marking<P>, IPredicate> getResult() {
		return mFloydHoareAnnotation;
	}

	public IPredicate getAssertion(final Marking<P> marking) {
		return mFloydHoareAnnotation.get(marking);
	}
}
