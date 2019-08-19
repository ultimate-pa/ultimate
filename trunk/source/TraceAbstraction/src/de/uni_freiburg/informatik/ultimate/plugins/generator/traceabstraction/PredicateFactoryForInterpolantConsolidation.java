/*
 * Copyright (C) 2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.AbstractMap;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PredicateFactoryForInterpolantConsolidation extends PredicateFactoryForInterpolantAutomata {

	private final Map<IPredicate, Set<IPredicate>> mLocationsToSetOfPredicates;
	private final Map<IPredicate, AbstractMap.SimpleEntry<IPredicate, IPredicate>> mIntersectedPredicateToArgumentPredicates;
	private final Map<AbstractMap.SimpleEntry<IPredicate, IPredicate>, IPredicate> mArgumentPredicatesToIntersectedPredicate;

	public PredicateFactoryForInterpolantConsolidation(final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final boolean taPrefs) {
		super(csToolkit.getManagedScript(), predicateFactory, taPrefs);
		mLocationsToSetOfPredicates = new HashMap<>();
		mIntersectedPredicateToArgumentPredicates = new HashMap<>();
		mArgumentPredicatesToIntersectedPredicate = new HashMap<>();
	}

	public Map<IPredicate, Set<IPredicate>> getLocationsToSetOfPredicates() {
		return mLocationsToSetOfPredicates;
	}

	/**
	 * Remove the predicates from the set of the consolidated predicates which only lead to a final state in the
	 * difference automaton.
	 * 
	 * @param badPredicates
	 *            - a set of states from the difference automaton
	 */
	public void removeBadPredicates(final Set<IPredicate> badPredicates) {
		for (final IPredicate p : badPredicates) {
			final AbstractMap.SimpleEntry<IPredicate, IPredicate> argumentPredicates =
					mIntersectedPredicateToArgumentPredicates.get(p);
			final Set<IPredicate> consolidatePredicates = mLocationsToSetOfPredicates.get(argumentPredicates.getKey());
			consolidatePredicates.remove(argumentPredicates.getValue());
		}
	}

	public IPredicate getIntersectedPredicate(final IPredicate argumentPredicate1,
			final IPredicate argumentPredicate2) {
		final AbstractMap.SimpleEntry<IPredicate, IPredicate> predicateArguments =
				new AbstractMap.SimpleEntry<>(argumentPredicate1, argumentPredicate2);
		return mArgumentPredicatesToIntersectedPredicate.get(predicateArguments);
	}

	@Override
	public IPredicate intersection(final IPredicate p1, final IPredicate p2) {
		// 1. Do the intersection
		assert p1 instanceof ISLPredicate;

		final IcfgLocation pp = ((ISLPredicate) p1).getProgramPoint();

		final Term conjunction = super.mPredicateFactory.and(p1, p2).getFormula();
		final IPredicate result = super.mPredicateFactory.newSPredicate(pp, conjunction);

		if (mIntersectedPredicateToArgumentPredicates.containsKey(result)) {
			throw new AssertionError("States of difference automaton are not unique!");
		}
		final AbstractMap.SimpleEntry<IPredicate, IPredicate> predicateArguments =
				new AbstractMap.SimpleEntry<>(p1, p2);
		mIntersectedPredicateToArgumentPredicates.put(result, predicateArguments);
		mArgumentPredicatesToIntersectedPredicate.put(predicateArguments, result);

		// 2. Store the predicates in the map
		if (mLocationsToSetOfPredicates.containsKey(p1)) {
			final Set<IPredicate> predicates = mLocationsToSetOfPredicates.get(p1);
			predicates.add(p2);
		} else {
			final Set<IPredicate> predicatesForThisLocation = new HashSet<>();
			predicatesForThisLocation.add(p2);
			mLocationsToSetOfPredicates.put(p1, predicatesForThisLocation);
		}
		return result;
	}

	public void removeConsolidatedPredicatesOnDifferentLevels(final Map<IPredicate, Integer> stateToLevel) {
		final int maxLevel = Collections.max(stateToLevel.values());
		for (final IPredicate loc : mLocationsToSetOfPredicates.keySet()) {
			final Set<IPredicate> consolidatedPreds = mLocationsToSetOfPredicates.get(loc);
			if (!consolidatedPreds.isEmpty()) {
				Set<IPredicate> predsToRemove = new HashSet<>();
				final int[] levelOccurrencesOfPredicates = new int[maxLevel];
				for (final IPredicate p : consolidatedPreds) {
					final IPredicate diffAutomatonState = getIntersectedPredicate(loc, p);
					final int lvlOfState = stateToLevel.get(diffAutomatonState);
					levelOccurrencesOfPredicates[lvlOfState - 1]++;
				}
				final int lvlThatOccursMost = getIndexOfMaxValue(levelOccurrencesOfPredicates);
				if (levelOccurrencesOfPredicates[lvlThatOccursMost - 1] <= 1) {
					predsToRemove = consolidatedPreds;
				} else {
					for (final IPredicate p : consolidatedPreds) {
						final IPredicate diffAutomatonState = getIntersectedPredicate(loc, p);
						final int lvlOfState = stateToLevel.get(diffAutomatonState);
						if (lvlOfState != lvlThatOccursMost) {
							predsToRemove.add(p);
						}
					}
				}
				// Remove states that occur on different levels than lvlThatOccursMost from consolidated predicates
				consolidatedPreds.removeAll(predsToRemove);
			}
		}
	}

	private static int getIndexOfMaxValue(final int[] levelOccurrencesOfPredicates) {
		int indexOfMaxValue = 0;
		for (int i = 1; i < levelOccurrencesOfPredicates.length; i++) {
			if (levelOccurrencesOfPredicates[i] > levelOccurrencesOfPredicates[indexOfMaxValue]) {
				indexOfMaxValue = i;
			}
		}
		return indexOfMaxValue;
	}
}
