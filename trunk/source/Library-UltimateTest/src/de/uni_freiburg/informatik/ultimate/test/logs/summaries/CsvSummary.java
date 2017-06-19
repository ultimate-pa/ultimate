/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.logs.summaries;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class CsvSummary extends BaseCsvProviderSummary {

	public CsvSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			final ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);

	}

	@Override
	public String getLog() {
		final StringBuilder sb = new StringBuilder();
		final PartitionedResults results = partitionResults(mResults.entrySet());
		final ICsvProvider<String> csvTotal = makePrintCsvProviderFromResults(results.All, mColumnDefinitions);
		csvTotal.toCsv(sb, null, true);
		sb.append(CoreUtil.getPlatformLineSeparator());
		return sb.toString();
	}

	@Override
	public String getFilenameExtension() {
		return ".csv";
	}
}
