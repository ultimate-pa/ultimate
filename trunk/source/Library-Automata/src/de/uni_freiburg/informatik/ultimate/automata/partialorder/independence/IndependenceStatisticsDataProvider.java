/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.independence;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IndependenceResultAggregator.Counter;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.PrettyPrint;

/**
 * Collects statistics for independence relations. Implementors of {@link IIndependenceRelation} can use this class to
 * implement {@link IIndependenceRelation#getStatistics()}.
 *
 * This class collects data on how many queries were made, with what result, and whether or not they were conditional.
 * If more data should be collected, derive a subclass and add the additional fields using the mechanism described in
 * {@link AbstractStatisticsDataProvider#declare(String, java.util.function.Supplier, KeyType)}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class IndependenceStatisticsDataProvider extends AbstractStatisticsDataProvider {

	public static final String INDEPENDENCE_QUERIES = "Independence Queries";
	public static final String UNDERLYING_RELATION = "Statistics on underlying relation";
	public static final String UNDERLYING_RELATIONS = "Statistics on underlying relations";

	private final Counter mQueryCounter = new Counter();

	/**
	 * Create a new instance to collect data, with the default data fields.
	 *
	 * @param clazz
	 *            The type of independence relation for which statistics are collected. This is used as a prefix for key
	 *            names in order to distinguish data for different, possibly nested relations.
	 */
	public IndependenceStatisticsDataProvider(final Class<?> clazz) {
		declareCounter(clazz.getSimpleName() + "." + INDEPENDENCE_QUERIES, () -> mQueryCounter);
	}

	/**
	 * Create a new instance to collect data, with the default data fields, and forward data on an underlying relation.
	 *
	 * @param clazz
	 *            The type of independence relation for which statistics are collected. This is used as a prefix for key
	 *            names in order to distinguish data for different, possibly nested relations.
	 * @param underlying
	 *            The underlying relation whose statistics shall be forwarded.
	 */
	public IndependenceStatisticsDataProvider(final Class<?> clazz, final IIndependenceRelation<?, ?> underlying) {
		this(clazz);
		forward(clazz.getSimpleName() + "." + UNDERLYING_RELATION, underlying::getStatistics);
	}

	/**
	 * Create a new instance to collect data, with the default data fields, and forward data on underlying relations.
	 *
	 * @param <S>
	 *            The condition type for the underlying relations
	 * @param <L>
	 *            The type of letters for the underlying relations
	 * @param clazz
	 *            The type of independence relation for which statistics are collected. This is used as a prefix for key
	 *            names in order to distinguish data for different, possibly nested relations.
	 * @param underlying
	 *            The underlying relations whose statistics shall be forwarded. The collection will only be traversed
	 *            when statistics are retrieved, so it is possible to pass a reference to a modifiable collections.
	 */
	public <S, L> IndependenceStatisticsDataProvider(final Class<?> clazz,
			final Iterable<IIndependenceRelation<S, L>> underlying) {
		this(clazz);
		forwardAll(clazz.getSimpleName() + "." + UNDERLYING_RELATIONS, underlying,
				IIndependenceRelation::getStatistics);
	}

	protected final void declareCounter(final String key, final Supplier<Counter> getter) {
		declare(key, getter::get, (x, y) -> Counter.sum((Counter) x, (Counter) y),
				(k, data) -> PrettyPrint.keyColonData(k, ((Counter) data).print(Object::toString)));
	}

	public Counter getQueries() {
		return mQueryCounter;
	}

	public void reportQuery(final Dependence result, final boolean conditional) {
		mQueryCounter.increment(result, conditional);
	}

	public void reportIndependentQuery(final boolean conditional) {
		mQueryCounter.increment(Dependence.INDEPENDENT, conditional);
	}

	public void reportDependentQuery(final boolean conditional) {
		mQueryCounter.increment(Dependence.DEPENDENT, conditional);
	}

	public void reportUnknownQuery(final boolean conditional) {
		mQueryCounter.increment(Dependence.UNKNOWN, conditional);
	}
}
