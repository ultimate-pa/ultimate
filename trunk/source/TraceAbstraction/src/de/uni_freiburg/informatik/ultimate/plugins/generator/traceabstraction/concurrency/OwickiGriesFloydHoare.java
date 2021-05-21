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

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

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

public class OwickiGriesFloydHoare<PLACE, LETTER> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final DefaultIcfgSymbolTable mSymbolTable;
	private final BasicPredicateFactory mFactory;
	private final Function<PLACE, IPredicate> mPlace2Predicate;

	private final BranchingProcess<LETTER, PLACE> mBp;
	private final IPetriNet<LETTER, PLACE> mNet;

	private final Set<Set<PLACE>> mCuts;
	private final Set<PLACE> mPlaces;
	private final Set<PLACE> mAssertPlaces;
	private final Set<PLACE> mOrigPlaces;
	private final Set<Set<PLACE>> mReach;

	private final Map<Marking<LETTER, PLACE>, IPredicate> mFloydHoareAnnotation;

	/**
	 * @TODO: assertion, places are IPredicate
	 * @param services
	 * @param csToolkit
	 * @param bp
	 * @param assertion
	 */
	public OwickiGriesFloydHoare(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final BranchingProcess<LETTER, PLACE> bp, final IPetriNet<LETTER, PLACE> net,
			final Function<PLACE, IPredicate> place2Predicate) {

		mServices = services;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mManagedScript = csToolkit.getManagedScript();
		mScript = mManagedScript.getScript();
		mSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
		mFactory = new BasicPredicateFactory(mServices, mManagedScript, mSymbolTable);
		mPlace2Predicate = place2Predicate;

		mBp = bp;
		mNet = net;

		mCuts = computeMaximalCosets(mBp);

		mPlaces = getPlaces(mCuts);
		mOrigPlaces = new HashSet<>(mNet.getPlaces());
		mAssertPlaces = getAssertPlaces(mPlaces, mOrigPlaces);
		mReach = getReach(mCuts);

		mFloydHoareAnnotation = getAnnotation();

	}

	public static <LETTER> OwickiGriesFloydHoare<IPredicate, LETTER> create(final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final BranchingProcess<LETTER, IPredicate> bp,
			final IPetriNet<LETTER, IPredicate> net) {
		return new OwickiGriesFloydHoare<>(services, csToolkit, bp, net, x -> x);
	}

	/**
	 * @param branching
	 *            process
	 * @return set of all maximal co-set (cuts) TODO: Set<Set<PLACE>>, no set of conditions?? labelling function? cCheck
	 *         branching def
	 */
	private static <LETTER, PLACE> Set<Set<PLACE>> computeMaximalCosets(final BranchingProcess<LETTER, PLACE> bp) {
		final Set<Set<PLACE>> maximalCoSets = new LinkedHashSet<>();
		for (final Event<LETTER, PLACE> event : bp.getEvents()) {
			// small optimization, cut-off event has same condition mark as companion
			if (!event.isCutoffEvent()) {
				maximalCoSets.add(event.getMark().stream().collect(Collectors.toSet()));
			}
		}
		return maximalCoSets;
	}

	private Map<Marking<LETTER, PLACE>, IPredicate> getAnnotation() {
		final Map<Marking<LETTER, PLACE>, IPredicate> mapping = new HashMap<>();
		for (final Set<PLACE> marking : mReach) {
			mapping.put(new Marking<LETTER, PLACE>(marking), getMarkingAssertion(marking));
		}
		return mapping;
	}

	// phi(d) = conjuct(assert(p)) for each p in z(d) (assertion places) -> Cut assertion
	private IPredicate getCutAssertion(final Set<PLACE> cut) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final PLACE place : getAssertPlaces(cut)) {
			predicates.add(mPlace2Predicate.apply(place));
		}
		return mFactory.and(predicates);
	}

	private IPredicate getMarkingAssertion(final Set<PLACE> marking) {
		final Set<IPredicate> predicates = new HashSet<>();
		for (final Set<PLACE> cut : getCuts(marking)) {
			predicates.add(getCutAssertion(cut));
		}
		return mFactory.or(predicates);
	}

	/**
	 * @param cuts
	 * @return set of all places in Petri Net* TODO: or get it as parameter from Net.getPlaces()
	 */
	private Set<PLACE> getPlaces(final Set<Set<PLACE>> cuts) {
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
	private Set<PLACE> getCutMarking(final Set<PLACE> cut) {
		final Set<PLACE> mark = new HashSet<>();
		for (final PLACE place : cut) {
			if (mOrigPlaces.contains(place)) {
				mark.add(place);
			}
		}
		return mark;
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
	private Set<Set<PLACE>> getReach(final Set<Set<PLACE>> Cuts) {
		final Set<Set<PLACE>> markings = new HashSet<>();
		for (final Set<PLACE> cut : Cuts) {
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

	public Map<Marking<LETTER, PLACE>, IPredicate> getResult() {
		return mFloydHoareAnnotation;
	}

	public IPredicate getAssertion(final Marking<LETTER, PLACE> marking) {
		return mFloydHoareAnnotation.get(marking);
	}

}
