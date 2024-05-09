/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Check a given Empire annotation for validity i.e. the initial markings law evaluates to true and every accepting
 * markings law evaluates to false. Further for all other markings m1, m2 must hold: If there is a firing relation f_t
 * between m1 and m2 then the Hoare-Triple {m1}t{m2} is valid.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public class EmpireValidityCheck<PLACE, LETTER extends IAction> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final ManagedScript mMgdScript;
	private final MonolithicImplicationChecker mImplicationChecker;
	private final MonolithicHoareTripleChecker mHc;
	private final BasicPredicateFactory mFactory;

	private final EmpireAnnotation<PLACE> mEmpireAnnotation;
	private final Map<IPredicate, PLACE> mPredicatePlaceMap;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mRefinedNet;
	private final Set<PLACE> mAssertionPlaces;
	private final PlacesCoRelation<PLACE> mPlacesCoRelation;
	private final Validity mValidity;

	public EmpireValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final MonolithicImplicationChecker implicationChecker, final BasicPredicateFactory factory,
			final IPetriNet<LETTER, PLACE> net, final IPetriNetSuccessorProvider<LETTER, PLACE> refinedNet,
			final ModifiableGlobalsTable modifiableGlobals, final EmpireAnnotation<PLACE> empire,
			final Map<IPredicate, PLACE> predicatePlaceMap, final Set<PLACE> assertionPlaces,
			final PlacesCoRelation<PLACE> placesCoRelation) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(EmpireValidityCheck.class);
		mMgdScript = mgdScript;
		mImplicationChecker = implicationChecker;
		mHc = new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals);
		mFactory = factory;

		mNet = net;
		mRefinedNet = refinedNet;
		mAssertionPlaces = assertionPlaces;
		mEmpireAnnotation = empire;
		mPredicatePlaceMap = predicatePlaceMap;
		mPlacesCoRelation = placesCoRelation;

		mValidity = checkValidity();
	}

	private Validity checkValidity() {

		final Set<Pair<Territory<PLACE>, IPredicate>> initialTerritories =
				mEmpireAnnotation.getMarkingTerritories(new Marking<>(ImmutableSet.copyOf(mNet.getInitialPlaces())));
		final var initialValidity = checkInitialTerritories(initialTerritories);
		if (initialValidity != Validity.VALID) {
			return Validity.INVALID;
		}
		if (checkSuccessorValidity(initialTerritories) != Validity.VALID) {
			return Validity.INVALID;
		}
		if (checkAcceptingPlaces() != Validity.VALID) {
			return Validity.INVALID;
		}
		return Validity.VALID;
	}

	private Validity checkInitialTerritories(final Set<Pair<Territory<PLACE>, IPredicate>> initialTerritories) {
		if (initialTerritories.isEmpty()) {
			mLogger.warn("Empire annotation does not contain any initial Territory");
			return Validity.INVALID;
		}
		final IPredicate trueIPredicate = mFactory.and();
		for (final Pair<Territory<PLACE>, IPredicate> pair : initialTerritories) {
			final Set<IPredicate> lawSet = mEmpireAnnotation.getLawSet(pair.getFirst());
			if (mImplicationChecker.checkImplication(trueIPredicate, false, mFactory.and(lawSet),
					false) != Validity.VALID) {
				mLogger.warn("Initial Territoriy maps to Law that does not evaluate to true:\n %s \n %s",
						pair.getFirst(), pair.getSecond());
				return Validity.INVALID;
			}
		}
		return Validity.VALID;
	}

	private Validity checkSuccessorValidity(final Set<Pair<Territory<PLACE>, IPredicate>> initialTerritories) {
		final Set<Pair<Territory<PLACE>, IPredicate>> visitedPairs = new HashSet<>();
		final var queue = new ArrayDeque<Pair<Territory<PLACE>, IPredicate>>(initialTerritories);
		while (!queue.isEmpty()) {
			final var pair = queue.poll();
			if (!visitedPairs.add(pair)) {
				continue;
			}
			final var territory = pair.getFirst();
			final var law = pair.getSecond();
			for (final var transition : (Iterable<Transition<LETTER, PLACE>>) territory.getEnabledTransitions(
					mRefinedNet, mPredicatePlaceMap.get(law), mAssertionPlaces, mPlacesCoRelation)::iterator) {
				final var predecessors = DataStructureUtils.difference(transition.getPredecessors(), mAssertionPlaces);
				final var successors = DataStructureUtils.difference(transition.getSuccessors(), mAssertionPlaces);
				final var bystanders = territory.getRegions().stream()
						.filter(r -> DataStructureUtils.haveEmptyIntersection(r.getPlaces(), predecessors))
						.collect(Collectors.toSet());
				final var equivalentTerritories = getEquivalentTerritories(transition, bystanders);
				final var lawConjunction = getLawConjunction(equivalentTerritories);
				final var successorPairs = mEmpireAnnotation.getSuccessorPairs(bystanders, successors);
				final List<Pair<Territory<PLACE>, IPredicate>> strongSuccessors =
						getStrongSuccessors(successorPairs, lawConjunction, transition, pair);
				final Validity successorValidity = strongSuccessors.isEmpty() ? Validity.INVALID : Validity.VALID;
				final Validity contradiction = checkContradiction(lawConjunction, transition, territory);
				if ((contradiction != Validity.VALID) && (successorValidity != Validity.VALID)) {
					return Validity.INVALID;
				}
				for (final Pair<Territory<PLACE>, IPredicate> pair2 : strongSuccessors) {
					queue.add(pair2);
				}
			}
		}

		if (!visitedPairs.equals(mEmpireAnnotation.getEmpire())) {
			mLogger.warn("Not all pairs are reachable from an initial pair. Unreachable pairs:\n %s",
					DataStructureUtils.difference(mEmpireAnnotation.getEmpire(), visitedPairs));
			return Validity.INVALID;
		}
		return Validity.VALID;
	}

	private Validity checkAcceptingPlaces() {
		final var acceptingPlaces = mNet.getAcceptingPlaces();
		for (final Pair<Territory<PLACE>, IPredicate> pair : mEmpireAnnotation.getEmpire()) {
			final var territory = pair.getFirst();
			final var law = pair.getSecond();
			if (DataStructureUtils.haveEmptyIntersection(territory.getPlaces(), acceptingPlaces)) {
				continue;
			}
			if (mImplicationChecker.checkImplication(law, false, mFactory.or(), false) != Validity.VALID) {
				mLogger.warn(
						"Territory: \n %s \n contains accepting places %s \n but the law %s does not evaluate to false.",
						territory, DataStructureUtils.intersection(territory.getPlaces(), acceptingPlaces), law);
				return Validity.INVALID;
			}
		}
		return Validity.VALID;
	}

	private boolean checkHoareTriple(final IPredicate pre, final IPredicate post,
			final Transition<LETTER, PLACE> transition) {
		final var valid = mHc.checkInternal(pre, (IInternalAction) transition.getSymbol(), post);
		return valid == Validity.VALID;
	}

	private Validity checkContradiction(final IPredicate lawConjunction, final Transition<LETTER, PLACE> transition,
			final Territory<PLACE> territory) {
		// final var transPredicate = mFactory.orT(transition.getSymbol().getTransformula().getFormula());
		// if (mImplicationChecker.checkImplication(lawConjunction, false, transPredicate, false) != Validity.VALID) {
		// return Validity.VALID;
		// }
		if (!checkHoareTriple(lawConjunction, mFactory.or(), transition)) {
			return Validity.INVALID;
		}
		return Validity.VALID;
	}

	List<Pair<Territory<PLACE>, IPredicate>> getStrongSuccessors(
			final Set<Pair<Territory<PLACE>, IPredicate>> successorPairs, final IPredicate lawConjunction,
			final Transition<LETTER, PLACE> transition, final Pair<Territory<PLACE>, IPredicate> pair) {
		final var result = new ArrayList<Pair<Territory<PLACE>, IPredicate>>();
		for (final Pair<Territory<PLACE>, IPredicate> succPair : successorPairs) {
			final var valid = checkHoareTriple(lawConjunction, succPair.getSecond(), transition);
			if (valid) {
				result.add(succPair);
			}
		}
		return result;
	}

	private Set<Pair<Territory<PLACE>, IPredicate>> getEquivalentTerritories(final Transition<LETTER, PLACE> transition,
			final Set<Region<PLACE>> bystanders) {
		final var result = new HashSet<Pair<Territory<PLACE>, IPredicate>>();
		for (final Pair<Territory<PLACE>, IPredicate> pair : mEmpireAnnotation.getEmpire()) {
			final var territory = pair.getFirst();
			final var law = pair.getSecond();
			if (!territory.getRegions().containsAll(bystanders) || !territory.enables(transition, mAssertionPlaces)) {
				continue;
			}
			result.add(pair);
		}
		return result;
	}

	private IPredicate getLawConjunction(final Set<Pair<Territory<PLACE>, IPredicate>> pairs) {
		final Set<IPredicate> lawSet = pairs.stream().map(p -> p.getSecond()).collect(Collectors.toSet());
		return mFactory.and(lawSet);
	}

	public Validity getValidity() {
		return mValidity;
	}
}
