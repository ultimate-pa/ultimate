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
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IndependenceResultAggregator.Timer;
import de.uni_freiburg.informatik.ultimate.util.statistics.PrettyPrint;

/**
 * Collects statistics for independence relation, in particular the (aggregated) time required for various kinds of
 * queries (conditional or not; positive, negative or unknown).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class TimedIndependenceStatisticsDataProvider extends IndependenceStatisticsDataProvider {
	public static final String QUERY_TIME = "Query Time";

	private final Timer mTimer = new Timer();

	/**
	 * Create a new instance with the default fields (number and required time for various kinds of queries).
	 *
	 * @param clazz
	 *            The type of independence relation for which statistics are collected. This is used as a prefix for key
	 *            names in order to distinguish data for different, possibly nested relations.
	 */
	public TimedIndependenceStatisticsDataProvider(final Class<?> clazz) {
		super(clazz);
		declareTimer(clazz.getSimpleName() + "." + QUERY_TIME, () -> mTimer);
	}

	protected final void declareTimer(final String key, final Supplier<Timer> getter) {
		declare(key, getter::get, (x, y) -> Timer.sum((Timer) x, (Timer) y), (k, data) -> PrettyPrint
				.keyColonData(k + " [ms]", ((Timer) data).print(t -> Long.toString(Math.round(t * 1e-6)))));
	}

	public void startQuery() {
		mTimer.start();
	}

	@Override
	public void reportQuery(final Dependence result, final boolean conditional) {
		mTimer.stop(result, conditional);
		super.reportQuery(result, conditional);
	}

	@Override
	public void reportIndependentQuery(final boolean conditional) {
		mTimer.stop(Dependence.INDEPENDENT, conditional);
		super.reportIndependentQuery(conditional);
	}

	@Override
	public void reportDependentQuery(final boolean conditional) {
		mTimer.stop(Dependence.DEPENDENT, conditional);
		super.reportDependentQuery(conditional);
	}

	@Override
	public void reportUnknownQuery(final boolean conditional) {
		mTimer.stop(Dependence.UNKNOWN, conditional);
		super.reportUnknownQuery(conditional);
	}
}
