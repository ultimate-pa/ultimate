/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.MinMaxMed;

public class EmpireStatistics extends AbstractStatisticsDataProvider {
	public static final String AUTOMATON_SIZE = "automaton size";
	public static final String UNIQUE_PAIRS = "number of unique pairs";
	public static final String LAW_SIZE = "empire law size";
	public static final String ANNOTATION_SIZE = "empire annotation size";
	public static final String REGION_COUNT = "number of regions";
	public static final String TERRITORY_COUNT = "number of territories";
	public static final String REGION_TERRITORY = "number of regions per territory";
	public static final String PLACES_PER_REGION = "number of places per region";

	private long mAutomatonSize;
	private long mNumberOfRegions;
	private long mNumberOfTerritories;
	private long mUniquePairs;
	private long mAnnotationSize;
	private final MinMaxMed mRegionsPerTerritory = new MinMaxMed();
	private final MinMaxMed mPlacesPerRegion = new MinMaxMed();

	public <P> EmpireStatistics(final IExplicitEmpire<?, ?, P> empire) {
		declareCounter(ANNOTATION_SIZE, () -> mAnnotationSize);
		declareCounter(AUTOMATON_SIZE, () -> mAutomatonSize);
		declareCounter(UNIQUE_PAIRS, () -> mUniquePairs);
		declareCounter(REGION_COUNT, () -> mNumberOfRegions);
		declareCounter(TERRITORY_COUNT, () -> mNumberOfTerritories);
		declareMinMaxMed(REGION_TERRITORY, mRegionsPerTerritory);
		declareMinMaxMed(PLACES_PER_REGION, mPlacesPerRegion);

		final var regions = empire.getStates().stream()
				.<Region<?>> flatMap(s -> empire.getTerritory(s).getRegions().stream()).collect(Collectors.toSet());
		final var territories = empire.getStates().stream().map(empire::getTerritory).collect(Collectors.toSet());

		mAnnotationSize = empire.getStates().stream().collect(Collectors.summingLong(s -> size(empire.getLaw(s))));
		mAutomatonSize = empire.getStates().size();
		mUniquePairs = empire.getStates().stream().map(s -> new Pair<>(empire.getTerritory(s), empire.getLaw(s)))
				.distinct().count();

		mNumberOfRegions = regions.size();
		mNumberOfTerritories = territories.size();

		mRegionsPerTerritory.report(territories, Territory::size);
		mPlacesPerRegion.report(regions, Region::size);
	}

	private long size(final IPredicate predicate) {
		if (predicate instanceof final PredicateWithConjuncts conjunction) {
			return conjunction.getConjuncts().stream().mapToLong(this::size).sum();
		}
		return new DAGSize().size(predicate.getFormula());
	}
}
