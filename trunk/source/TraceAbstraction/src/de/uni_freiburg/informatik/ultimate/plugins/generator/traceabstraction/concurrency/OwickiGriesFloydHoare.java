/*
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Constructs an Floyd Hoare annotation from a Branching process of the Final refined Petri Net.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public class OwickiGriesFloydHoare<PLACE extends IPredicate, LETTER extends IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final DefaultIcfgSymbolTable mSymbolTable;
	private final BasicPredicateFactory mFactory;
	private final Function<PLACE, IPredicate> mPlace2Predicate;
	private final List<IRefinementEngineResult<LETTER, ?>> mRefinementEngines;
	private final boolean mCoveringSimplification;

	private final BranchingProcess<LETTER, PLACE> mBp;
	private final IPetriNet<LETTER, PLACE> mNet;

	private final Set<Condition<LETTER, PLACE>> mConditions;
	private final Set<Condition<LETTER, PLACE>> mOrigConditions;
	private final Set<Condition<LETTER, PLACE>> mAssertConditions;

	private final Set<ImmutableSet<PLACE>> mCuts;
	private final Set<PLACE> mPlaces;
	private final Set<PLACE> mAssertPlaces;
	private final Set<PLACE> mOrigPlaces;
	private final Set<ImmutableSet<PLACE>> mReach;
	private final Set<ImmutableSet<Condition<LETTER, PLACE>>> mMarkingCosets = new HashSet<>();

	private final Map<Marking<PLACE>, IPredicate> mFloydHoareAnnotation;

	/**
	 * @TODO: assertion, places are IPredicate
	 * @param services
	 * @param csToolkit
	 * @param bp
	 * @param assertion
	 */
	public OwickiGriesFloydHoare(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final BranchingProcess<LETTER, PLACE> bp, final IPetriNet<LETTER, PLACE> net,
			final Function<PLACE, IPredicate> place2Predicate,
			final List<IRefinementEngineResult<LETTER, ?>> refinementEngines, final boolean iterativeCosets,
			final boolean coveringSimplification) {

		mServices = services;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mManagedScript = csToolkit.getManagedScript();
		mScript = mManagedScript.getScript();
		mSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
		mFactory = new BasicPredicateFactory(mServices, mManagedScript, mSymbolTable);
		mPlace2Predicate = place2Predicate;
		mRefinementEngines = refinementEngines;

		mBp = bp;
		mNet = net;

		mCuts = computeMaximalCosets(mBp);

		mOrigPlaces = new HashSet<>(mNet.getPlaces());
		mConditions = mBp.getConditions().stream().collect(Collectors.toSet());
		mOrigConditions = getOrigConditions();
		mAssertConditions = DataStructureUtils.difference(mConditions, mOrigConditions);

		mPlaces = getPlaces(mCuts);
		mAssertPlaces = getAssertPlaces(mPlaces, mOrigPlaces);
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
	private Map<Marking<PLACE>, IPredicate> getMaximalAnnotation() {
		final Map<Marking<PLACE>, IPredicate> mapping = new HashMap<>();
		for (final ImmutableSet<PLACE> marking : mReach) {
			mapping.put(new Marking<>(marking), getMarkingAssertion(marking));
		}
		return mapping;
	}

	/**
	 * Cuts computation from "greedy" algorithm With simplification
	 */
	private Map<Marking<PLACE>, IPredicate> getCosetAnnotation() {
		final Map<Marking<PLACE>, IPredicate> mapping = new HashMap<>();
		final Set<Set<Condition<LETTER, PLACE>>> markingCosets = getCosets(new HashSet<Condition<LETTER, PLACE>>(),
				new HashSet<Condition<LETTER, PLACE>>(), mOrigConditions, new HashSet<Set<Condition<LETTER, PLACE>>>());
		for (final Set<Condition<LETTER, PLACE>> markCoset : markingCosets) {
			final ImmutableSet<PLACE> markPlaces = getCosetPlaces(markCoset);
			final Set<Set<Condition<LETTER, PLACE>>> assertConds = getCosets(new HashSet<Condition<LETTER, PLACE>>(),
					markCoset, mAssertConditions, new HashSet<Set<Condition<LETTER, PLACE>>>());
			final Set<Set<IPredicate>> markAssertPlaces = new HashSet<>();
			for (final Set<Condition<LETTER, PLACE>> assertCond : assertConds) {
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

	private ImmutableSet<PLACE> getCosetPlaces(final Set<Condition<LETTER, PLACE>> coset) {
		final Set<PLACE> placeCoset = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : coset) {
			placeCoset.add(condition.getPlace());
		}
		return ImmutableSet.of(placeCoset);

	}

	private Set<IPredicate> getCosetPredicates(final Set<Condition<LETTER, PLACE>> coset) {
		final Set<IPredicate> predCoset = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : coset) {
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
		for (final IRefinementEngineResult<?, ?> refEngine : mRefinementEngines) {
			condImplications.addAll(DataStructureUtils.intersection(assertConditions,
					refEngine.getPredicateUnifier().getCoverageRelation().getCoveringPredicates(condition)));
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
		for (final IRefinementEngineResult<?, ?> refEngine : mRefinementEngines) {
			final Set<IPredicate> coveredPlaces =
					refEngine.getPredicateUnifier().getCoverageRelation().getCoveredPredicates(condition);
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
	private Set<Set<Condition<LETTER, PLACE>>> getCosets(final Set<Condition<LETTER, PLACE>> coset,
			final Set<Condition<LETTER, PLACE>> compCoset, final Set<Condition<LETTER, PLACE>> conditions,
			Set<Set<Condition<LETTER, PLACE>>> cuts) {
		final Set<Condition<LETTER, PLACE>> toAdd = DataStructureUtils.difference(conditions, coset);
		final Set<Set<Condition<LETTER, PLACE>>> cosets = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : toAdd) {
			if (mBp.getCoRelation().isCoset(compCoset, cond) & mBp.getCoRelation().isCoset(coset, cond)) {
				final Set<Condition<LETTER, PLACE>> imCoset =
						DataStructureUtils.union(coset, DataStructureUtils.toSet(cond));
				cosets.add(imCoset);
			}
		}
		if (!cosets.isEmpty()) {
			for (final Set<Condition<LETTER, PLACE>> imcoset : cosets) {
				cuts = DataStructureUtils.union(cuts, getCosets(imcoset, compCoset, conditions, cuts));
			}
		} else {
			cuts.add(coset);
		}
		return cuts;
	}

	private Set<Condition<LETTER, PLACE>> getOrigConditions() {
		final Set<Condition<LETTER, PLACE>> conditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : mBp.getConditions()) {
			if (mOrigPlaces.contains(cond.getPlace())) {
				conditions.add(cond);
			}
		}
		return conditions;
	}

	private IPredicate getMarkingAssertion(final Set<PLACE> marking) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final Set<PLACE> cut : getCuts(marking)) {
			predicates.add(getCutAssertion(cut, getAssertPlaces(cut)));
		}
		return mFactory.or(predicates);
	}

	private IPredicate getCutAssertion(final Set<PLACE> cut, final Set<PLACE> assertPlaces) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final IPredicate place : assertPlaces) {
			predicates.add(place);
		}
		return mFactory.and(predicates);
	}

	// Call this for simple and "greedy" cuts Annotation
	private IPredicate getMarkingAssertion(final Set<PLACE> marking, final Set<Set<IPredicate>> cuts) {
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
	private Set<PLACE> getPlaces(final Set<ImmutableSet<PLACE>> cuts) {
		final Set<PLACE> places = new HashSet<>();
		for (final Set<PLACE> cut : cuts) {
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
	private Set<PLACE> getAssertPlaces(final Set<PLACE> places, final Set<PLACE> origPlaces) {
		return DataStructureUtils.difference(places, origPlaces);
	}

	/**
	 * @param cut
	 * @return mark, set of original places in cut
	 */
	private ImmutableSet<PLACE> getCutMarking(final Set<PLACE> cut) {
		final Set<PLACE> mark = new HashSet<>();
		for (final PLACE place : cut) {
			if (mOrigPlaces.contains(place)) {
				mark.add(place);
			}
		}
		return ImmutableSet.of(mark);
	}

	/**
	 * @param cut
	 * @return set of all assertion places in cut
	 */
	private Set<PLACE> getAssertPlaces(final Set<PLACE> cut) {
		final Set<PLACE> places = new HashSet<>();
		for (final PLACE place : cut) {
			if (mAssertPlaces.contains(place)) {
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
	private Set<ImmutableSet<PLACE>> getReach(final Set<ImmutableSet<PLACE>> Cuts) {
		final Set<ImmutableSet<PLACE>> markings = new HashSet<>();
		for (final ImmutableSet<PLACE> cut : Cuts) {
			markings.add(getCutMarking(cut));
		}
		return markings;
	}

	/**
	 * @param marking
	 * @return set of cuts that have marking as original marking
	 */
	private Set<Set<PLACE>> getCuts(final Set<PLACE> marking) {
		final Set<Set<PLACE>> cuts = new HashSet<>();
		for (final Set<PLACE> cut : mCuts) {
			if (marking.equals(getCutMarking(cut))) {
				cuts.add(cut);
			}
		}
		return cuts;
	}

	public Map<Marking<PLACE>, IPredicate> getResult() {
		return mFloydHoareAnnotation;
	}

	public IPredicate getAssertion(final Marking<PLACE> marking) {
		return mFloydHoareAnnotation.get(marking);
	}

}
