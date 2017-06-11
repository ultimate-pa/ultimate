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
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.statistics.GraphSizeCsvProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgSizeBenchmark {
	
	private final GraphSizeCsvProvider mCsvProvider;
	
	public IcfgSizeBenchmark(final IIcfg<?> root, final String label) {
		final Deque<IcfgEdge> edges = new ArrayDeque<>();
		final Set<IcfgEdge> closedE = new HashSet<>();
		final Set<IcfgLocation> closedV = new HashSet<>();
		
		edges.addAll(root.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream())
				.collect(Collectors.toSet()));
		edges.stream().forEach(e -> closedV.add(e.getSource()));
		
		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (closedE.contains(current)) {
				continue;
			}
			closedE.add(current);
			
			if (current.getTarget() == null) {
				throw new AssertionError("Target may not be null");
			}
			
			closedV.add(current.getTarget());
			for (final IcfgEdge next : current.getTarget().getOutgoingEdges()) {
				edges.add(next);
			}
		}
		
		mCsvProvider = new GraphSizeCsvProvider(closedE.size(), closedV.size(), label);
	}
	
	@Override
	public String toString() {
		return mCsvProvider.toString();
	}
	
	public void reportBenchmarkResult(final IResultService resultService, final String pluginId, final String message) {
		resultService.reportResult(pluginId, new de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult<>(
				pluginId, message, mCsvProvider));
	}
}
