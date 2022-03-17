/*
 * Copyright (C) 2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class StatisticsAggregationService {

	private static final String PATH_SEPARATOR = "/";
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Map<String, Set<Supplier<IStatisticsDataProvider>>> mStats;
	private final Lazy<IStatisticsDataProvider> mAggregatedStatistics;
	private boolean mIsClosed;

	public StatisticsAggregationService(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(StatisticsAggregationService.class);
		mStats = new LinkedHashMap<>();
		mAggregatedStatistics = new Lazy<>(this::createAggregation);
	}

	public IStatisticsDataProvider aggregateAll() {
		return mAggregatedStatistics.get();
	}

	private IStatisticsDataProvider createAggregation() {
		mIsClosed = true;
		final StatisticsAggregator rtr = new StatisticsAggregator();
		for (final Entry<String, Set<Supplier<IStatisticsDataProvider>>> entry : mStats.entrySet()) {
			final StatisticsAggregator leaf = new StatisticsAggregator(mServices.getStorage());
			entry.getValue().stream().map(Supplier::get).collect(Collectors.toSet()).stream().forEach(a -> {
				leaf.aggregateStatisticsData(a);
				mLogger.debug("Aggregated %s", a);
			});
			final String[] path = entry.getKey().split(PATH_SEPARATOR);
			aggregate(path, 0, rtr, leaf);
		}
		mStats.clear();
		return rtr;
	}

	private void aggregate(final String[] path, final int idx, final StatisticsAggregator currentRoot,
			final StatisticsAggregator data) {
		if (idx + 1 == path.length) {
			currentRoot.aggregateStatisticsData(path[idx], data);
		} else {
			final StatisticsAggregator nextRoot = new StatisticsAggregator(mServices.getStorage());
			aggregate(path, idx + 1, nextRoot, data);
			currentRoot.aggregateStatisticsData(path[idx], nextRoot);
		}
	}

	public void register(final Supplier<IStatisticsDataProvider> sdp, final String... pathSegments) {
		if (mIsClosed) {
			throw new IllegalStateException();
		}
		final String path = Arrays.stream(pathSegments).collect(Collectors.joining(PATH_SEPARATOR));
		mLogger.debug("Registering statistics aggregation to %s", path);
		mStats.computeIfAbsent(path, a -> new HashSet<>()).add(sdp);
	}

}
