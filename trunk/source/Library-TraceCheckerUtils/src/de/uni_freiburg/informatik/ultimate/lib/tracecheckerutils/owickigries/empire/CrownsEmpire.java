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

import java.util.HashMap;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.Crown;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.Rook;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * Construct an Empire annotation from a Crown.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public class CrownsEmpire<PLACE, LETTER> {
	private final Crown<PLACE, LETTER> mCrown;
	private final EmpireAnnotation<PLACE, LETTER> mEmpireAnnotation;

	private final Statistics mStatistics = new Statistics();

	/**
	 * Takes a crown and constructs an empire from it.
	 *
	 * @param crown
	 *            Crown to construct an empire of
	 * @param factory
	 *            Factory for operations on IPredicate
	 * @param placeToAssertion
	 *            Function which maps PLACE to the corresponding assertion
	 */
	public CrownsEmpire(final Crown<PLACE, LETTER> crown, final BasicPredicateFactory factory,
			final Function<PLACE, IPredicate> placeToAssertion) {
		mCrown = crown;
		mEmpireAnnotation = constructEmpireAnnotation(factory, placeToAssertion);
		mStatistics.reportEmpire(mEmpireAnnotation);
	}

	private EmpireAnnotation<PLACE, LETTER> constructEmpireAnnotation(final BasicPredicateFactory factory,
			final Function<PLACE, IPredicate> placeToAssertion) {
		final HashMap<Territory<PLACE, LETTER>, TerritoryLaw<PLACE, LETTER>> crownsTerritories = new HashMap<>();
		for (final Rook<PLACE, LETTER> rook : mCrown.getRooks()) {
			final Territory<PLACE, LETTER> rookTerritory = new Territory<>(rook.getKingdom());
			if (!crownsTerritories.containsKey(rookTerritory)) {
				final TerritoryLaw<PLACE, LETTER> law =
						new TerritoryLaw<>(rookTerritory, rook.getLaw(), placeToAssertion, factory);
				crownsTerritories.put(rookTerritory, law);
				continue;
			}
			final TerritoryLaw<PLACE, LETTER> law = crownsTerritories.remove(rookTerritory);
			law.addRooksAssertion(rook.getLaw());
			crownsTerritories.put(rookTerritory, law);
		}
		final EmpireAnnotation<PLACE, LETTER> empireAnnotation = new EmpireAnnotation<>(crownsTerritories);
		return empireAnnotation;
	}

	public EmpireAnnotation<PLACE, LETTER> getEmpireAnnotation() {
		return mEmpireAnnotation;
	}

	public Crown<PLACE, LETTER> getCrown() {
		return mCrown;
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends AbstractStatisticsDataProvider {
		public static final String EMPIRE_SIZE = "empire size";
		public static final String LAW_SIZE = "empire law size";
		public static final String ANNOTATION_SIZE = "empire annotation size";
		public static final String REGION_COUNT = "number of regions";

		private long mEmpireSize;
		private long mLawSize;
		private long mAnnotationSize;
		private long mRegionCount;

		public Statistics() {
			declare(EMPIRE_SIZE, () -> mEmpireSize, KeyType.COUNTER);
			declare(LAW_SIZE, () -> mLawSize, KeyType.COUNTER);
			declare(ANNOTATION_SIZE, () -> mAnnotationSize, KeyType.COUNTER);
			declare(REGION_COUNT, () -> mRegionCount, KeyType.COUNTER);
		}

		private void reportEmpire(final EmpireAnnotation<?, ?> empireAnnotation) {
			mRegionCount = empireAnnotation.getRegionCount();
			mEmpireSize = empireAnnotation.getEmpireSize();
			mLawSize = empireAnnotation.getLawSize();
			mAnnotationSize = empireAnnotation.getAnnotationSize();
		}
	}
}
