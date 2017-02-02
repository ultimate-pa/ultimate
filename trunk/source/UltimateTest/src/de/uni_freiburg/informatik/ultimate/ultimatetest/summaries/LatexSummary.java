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
package de.uni_freiburg.informatik.ultimate.ultimatetest.summaries;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class LatexSummary extends BaseCsvProviderSummary {

	public LatexSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);
	}

	protected Set<String> getDistinctFolderSuffixes(PartitionedResults results) {
		final Set<File> folders = results.All.stream().flatMap(c -> Arrays.stream(c.getKey().getInput()))
				.map(a -> a.getParentFile()).collect(Collectors.toSet());

		final Set<String[]> working = new HashSet<>();

		for (final File folder : folders) {
			working.add(folder.getAbsolutePath().split(Pattern.quote(File.separator)));
		}
		int offset = 0;
		boolean offsetsEqual = false;
		while (!offsetsEqual) {
			offsetsEqual = true;
			String last = null;
			for (final String[] pathSegments : working) {
				String currentlast = File.separator;
				final int end = pathSegments.length - 1;
				int j = end - offset;

				while (j <= end) {
					currentlast += pathSegments[j] + File.separator;
					++j;
				}

				if (!currentlast.equals(last)) {
					last = currentlast;
				} else {
					offset++;
					offsetsEqual = false;
					break;
				}
			}
		}

		final HashSet<String> rtr = new HashSet<>();
		for (final String[] pathSegments : working) {
			String suffix = "";
			for (int i = pathSegments.length - 1 - offset; i < pathSegments.length; ++i) {
				suffix += pathSegments[i] + File.separator;
			}
			suffix = suffix.substring(0, suffix.length() - File.separator.length());
			rtr.add(suffix);
		}
		assert rtr.size() == folders.size();

		return rtr;
	}

	protected boolean isInvalidForLatex(String cell) {
		return cell == null || cell.contains("[");
	}

	protected String removeInvalidCharsForLatex(String cell) {
		return cell.replace("\\", "{\\textbackslash}").replace("_", "\\_");
	}

}
