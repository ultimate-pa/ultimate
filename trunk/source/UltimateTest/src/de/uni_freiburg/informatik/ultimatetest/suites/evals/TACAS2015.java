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
package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;

public abstract class TACAS2015 extends AbstractEvalTestSuite {

	@Override
	protected long getTimeout() {
		return 300 * 1000;
	}

	protected String[] getDirectories() {
		// @formatter:off
		String[] directories = {
			"examples/svcomp/ntdrivers-simplified/",
	   		"examples/svcomp/ssh-simplified/", 
			"examples/svcomp/locks/",
			"examples/svcomp/recursive/", 
			"examples/svcomp/systemc/",
		};
		return directories;
		// @formatter:on
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[]{
				new ColumnDefinition(
						"Runtime (ns)", "Avg. runtime",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
				new ColumnDefinition(
						"Peak memory consumption (bytes)", "Mem{-}ory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),						
				new ColumnDefinition(
						"Overall iterations", "Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"NumberOfCodeBlocks", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"SizeOfPredicatesFP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
				new ColumnDefinition(
						"SizeOfPredicatesBP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
				new ColumnDefinition(
						"Conjuncts in SSA", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
				new ColumnDefinition(
						"Conjuncts in UnsatCore", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"ICC %", "ICC",
						ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average),					
			};
		// @formatter:on
	}

	protected int getFilesPerDirectory() {
		return Integer.MAX_VALUE;
	}

	protected String[] getFileEndings() {
		return new String[] { ".c" };
	}

	protected DirectoryFileEndingsPair getPair(String directory, int limit) {
		return new DirectoryFileEndingsPair(directory, getFileEndings(), limit);
	}

	protected DirectoryFileEndingsPair getPair(String directory) {
		return new DirectoryFileEndingsPair(directory, getFileEndings());
	}

	protected DirectoryFileEndingsPair[] getPairs(int limit) {
		List<DirectoryFileEndingsPair> rtr = new ArrayList<>();
		for (String directory : getDirectories()) {
			rtr.add(getPair(directory, limit));
		}
		return rtr.toArray(new DirectoryFileEndingsPair[rtr.size()]);
	}

	protected DirectoryFileEndingsPair[] getPairs() {
		List<DirectoryFileEndingsPair> rtr = new ArrayList<>();
		for (String directory : getDirectories()) {
			rtr.add(getPair(directory));
		}
		return rtr.toArray(new DirectoryFileEndingsPair[rtr.size()]);
	}

}
