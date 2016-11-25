/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class GraphSizeCsvProvider implements ICsvProviderProvider<Integer> {

	private final int mEdges;
	private final int mLocations;
	private final String mLabel;

	public GraphSizeCsvProvider(final int edges, final int nodes, final String label) {
		mEdges = edges;
		mLocations = nodes;
		mLabel = label;
	}

	@Override
	public ICsvProvider<Integer> createCsvProvider() {
		final List<String> columnTitles = new ArrayList<>();
		columnTitles.add(mLabel + " Locations");
		columnTitles.add(mLabel + " Edges");

		final List<Integer> row = new ArrayList<>();
		row.add(mLocations);
		row.add(mEdges);

		final SimpleCsvProvider<Integer> rtr = new SimpleCsvProvider<>(columnTitles);
		rtr.addRow(row);
		return rtr;
	}

	@Override
	public String toString() {
		return String.valueOf(mLocations) + " locations, " + String.valueOf(mEdges) + " edges";
	}
}