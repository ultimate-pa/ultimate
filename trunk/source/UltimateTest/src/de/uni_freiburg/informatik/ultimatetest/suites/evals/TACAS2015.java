package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.ArrayList;
import java.util.List;

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
