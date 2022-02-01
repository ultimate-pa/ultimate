/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.util.statistics.GraphSizeCsvProvider;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class NestedWordAutomataSizeBenchmark<E, V> {

	private final GraphSizeCsvProvider mCsvProvider;

	public NestedWordAutomataSizeBenchmark(final INestedWordAutomaton<E, V> nwa, final String label) {
		final Collection<V> states = nwa.getStates();
		int edges = 0;
		int locs = 0;
		for (final V state : states) {
			++locs;
			for (final OutgoingInternalTransition<E, V> out : nwa.internalSuccessors(state)) {
				++edges;
			}
			for (final OutgoingCallTransition<E, V> out : nwa.callSuccessors(state)) {
				++edges;
			}
			for (final OutgoingReturnTransition<E, V> out : nwa.returnSuccessors(state)) {
				++edges;
			}
			for (final SummaryReturnTransition<E, V> out : nwa.summarySuccessors(state)) {
				++edges;
			}
		}
		mCsvProvider = new GraphSizeCsvProvider(edges, locs, label);
	}

	@Override
	public String toString() {
		return mCsvProvider.toString();
	}

	public void reportBenchmarkResult(final IResultService resultService, final String pluginId, final String message) {
		resultService.reportResult(pluginId, new StatisticsResult<>(pluginId, message, mCsvProvider));
	}
}
