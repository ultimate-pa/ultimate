/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.NoTimeoutTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.StandingsSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractModelCheckerTestSuite;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class IntBlastingWrapperSmtcomp2023 extends AbstractModelCheckerTestSuite {

	/* The following two fields allow us to limit the number of files per
	 * directory.
	 * First all files of each directory are shuffled in a pseudorandom way
	 * then all files are listed and we take the files from position
	 * FILE_OFFSET to the position (FILE_OFFSET+FILES_PER_DIRECTORY_LIMIT).
	 * This means that FILES_PER_DIRECTORY_LIMIT defines the size
	 * of the interval that we take and FILE_OFFSET defines which interval
	 * we take.
	 */
	 private static final int FILES_PER_DIRECTORY_LIMIT = 100;
	 private static final int FILE_OFFSET = 0;

	// @formatter:off
	private static final String SMT_FILEENDING = ".*smt2";


	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {
			new DirectoryFileEndingsPair("examples/local/2022smtcomp/BV", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2022smtcomp/ABV", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2022smtcomp/UFBV", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
	};


	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}

	/**
	 * List of path to setting files. Ultimate will run on each program with each setting that is defined here. The path
	 * are defined relative to the folder "trunk/examples/settings/", because we assume that all settings files are in
	 * this folder.
	 *
	 */
	private static final String[] mSettings = {
			"IntBlastingWrapper/smtinterpolRangeBased.epf",
			"IntBlastingWrapper/smtinterpolCongruenceBased.epf",
	};

	private static final String[] mCToolchains = {
			"Empty.xml",
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : mDirectoryFileEndingsPairs) {
			for (final String toolchain : mCToolchains) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), mSettings, toolchain, getTimeout(),
						dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCases();
	}


	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new NoTimeoutTestResultDecider(ultimateRunDefinition);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] { new TraceAbstractionTestSummary(this.getClass()),
				new StandingsSummary(this.getClass()), };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { new IncrementalLogWithBenchmarkResults(this.getClass()),
				new IncrementalLogWithVMParameters(this.getClass(), getTimeout()), };
	}
	// @formatter:on

}

