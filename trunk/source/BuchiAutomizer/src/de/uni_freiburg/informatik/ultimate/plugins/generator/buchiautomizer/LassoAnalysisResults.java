/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class LassoAnalysisResults implements IStatisticsDataProvider, IStatisticsType {
	public static final String LASSO_NONTERMINATING = "nont";
	public static final String TERMINATION_UNKNOWN = "unkn";
	/**
	 * Cases where (already a single iteration of) the loop is infeasible.
	 */
	public static final String STEM_FEASIBLE_LOOP_INFEASIBLE = "SFLI";
	/**
	 * Cases where the stem is feasible, (a single iteration of) the loop is feasible but the loop is terminating.
	 */
	public static final String STEM_FEASIBLE_LOOP_TERMINATING = "SFLT";
	/**
	 * Cases where stem and loop are feasible but the concatenation of stem and loop is infeasible.
	 */
	public static final String CONCATENATION_INFEASIBLE = "conc";
	/**
	 * Cases where stem and loop are feasible but the concatenation of stem and loop is infeasible and the loop is
	 * terminating.
	 */
	public static final String CONCATENATION_INFEASIBLE_LOOP_TERMINATING = "concLT";
	/**
	 * Cases where the stem is infeasible and the loop is nonterminating.
	 */
	public static final String STEM_INFEASIBLE_LOOP_NONTERMINATING = "SILN";
	/**
	 * Cases where the stem is infeasible and the termination/feasibility of the loop is unknown.
	 */
	public static final String STEM_FEASIBLE_LOOP_UNKNOWN = "SILU";
	/**
	 * Cases where the stem is infeasible and the loop is infeasible.
	 */
	public static final String STEM_INFEASIBLE_LOOP_INFEASIBLE = "SILI";
	/**
	 * Cases where both, stem and loop are infeasible.
	 */
	public static final String STEM_INFEASIBLE_LOOP_TERMINATING = "SILT";
	/**
	 * Cases where the stem and the loop are feasible, the loop itself is nonterminating but the lasso is terminating.
	 */
	public static final String LASSO_TERMINATING = "lasso";

	private final Map<String, Integer> mMap;

	public LassoAnalysisResults() {
		mMap = new LinkedHashMap<>();
		mMap.put(LASSO_NONTERMINATING, 0);
		mMap.put(TERMINATION_UNKNOWN, 0);
		mMap.put(STEM_FEASIBLE_LOOP_INFEASIBLE, 0);
		mMap.put(STEM_FEASIBLE_LOOP_TERMINATING, 0);
		mMap.put(CONCATENATION_INFEASIBLE, 0);
		mMap.put(CONCATENATION_INFEASIBLE_LOOP_TERMINATING, 0);
		mMap.put(STEM_INFEASIBLE_LOOP_NONTERMINATING, 0);
		mMap.put(STEM_FEASIBLE_LOOP_UNKNOWN, 0);
		mMap.put(STEM_INFEASIBLE_LOOP_INFEASIBLE, 0);
		mMap.put(STEM_INFEASIBLE_LOOP_TERMINATING, 0);
		mMap.put(LASSO_TERMINATING, 0);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final String key : getKeys()) {
			sb.append(key);
			sb.append(getValue(key));
			sb.append(" ");
		}
		return sb.toString();
	}

	public void increment(final String key) {
		final int value = mMap.get(key);
		mMap.put(key, value + 1);
	}

	@Override
	public Collection<String> getKeys() {
		return mMap.keySet();
	}

	@Override
	public Object getValue(final String key) {
		return mMap.get(key);
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return this;
	}

	@Override
	public Object aggregate(final String key, final Object value1, final Object value2) {
		throw new AssertionError("not yet implemented");
	}

	@Override
	public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
		final LassoAnalysisResults lar = (LassoAnalysisResults) benchmarkData;
		final StringBuilder sb = new StringBuilder();
		for (final String key : lar.getKeys()) {
			sb.append(key);
			sb.append(lar.getValue(key));
			sb.append(" ");
		}
		return sb.toString();
	}

}
