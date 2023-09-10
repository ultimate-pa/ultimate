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
	 private static final int FILES_PER_DIRECTORY_LIMIT = 10;
	 private static final int FILE_OFFSET = 0;

	// @formatter:off
	private static final String SMT_FILEENDING = ".*smt2";


	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {


			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/2018-Mann", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/2019-Mann", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/2019-Wolf-fmbench", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/20200415-Yurichev", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/20230321-UltimateAutomizerSvcomp2023", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/bench_ab", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/bmc-arrays", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/brummayerbiere", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/brummayerbiere2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/brummayerbiere3", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/btfnt", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/calc2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/dwp_formulas", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/ecc", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/egt", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/jager", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/klee-selected-smt2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/pipe", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/platania", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/sharing-is-caring", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/stp", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_ABV/stp_samples", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),


			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20170501-Heizmann-UltimateAutomizer", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20170531-Hansen-Check", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/2017-BuchwaldFried", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/2018-Goel-hwbench", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/2018-Mann", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20190311-bv-term-small-rw-Noetzli", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20190429-UltimateAutomizerSvcomp2019", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/2019-Mann", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/2019-Wolf-fmbench", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20200328-Favaro", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20200415-Yurichev", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/2020-Weber", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20210219-Sydr", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20210312-Bouvier", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20220315-ecrw", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20230221-oisc-gurtner", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20230224-grsbits-truby", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/20230321-UltimateAutomizerSvcomp2023", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/asp", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/bench_ab", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/bmc-bv", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/bmc-bv-svcomp14", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/brummayerbiere", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/brummayerbiere2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/brummayerbiere3", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/brummayerbiere4", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/bruttomesso", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/calypto", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/challenge", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/check2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/crafted", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/dwp_formulas", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/ecc", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/fft", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/float", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/galois", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/gulwani-pldi08", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/log-slicing", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/mcm", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/pipe", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/pspace", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/rubik", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/RWS", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/sage", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/Sage2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/spear", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/stp", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/stp_samples", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/tacas07", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/uclid", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/uclid_contrib_smtcomp09", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/uum", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/VS3", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_BV/wienand-cav2008", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),

			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_UFBV/2018-Goel-hwbench", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_UFBV/2019-Wolf-fmbench", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_UFBV/20210312-Bouvier", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_UFBV/20230314-Jaroslav-Bendik-Certora", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_UFBV/btfnt", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/QF_UFBV/calc2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),

			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/20170501-Heizmann-UltimateAutomizer", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/2017-Preiner-keymaera", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/2017-Preiner-psyco", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/2017-Preiner-scholl-smt08", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/2017-Preiner-tptp", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/2017-Preiner-UltimateAutomizer", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/2018-Preiner-cav18", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/20190429-UltimateAutomizerSvcomp2019", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/2020-Preiner-fmcad20", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/20210301-Alive2", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/20210301-Alive2-partial-undef", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/20210330-PEak", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/20230321-UltimateAutomizerSvcomp2023", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/llvm13-smtlib", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
			new DirectoryFileEndingsPair("examples/local/2023smtcomp/BV/wintersteiger", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),

//			new DirectoryFileEndingsPair("examples/local/2019smtcomp/QF_BV", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
//			new DirectoryFileEndingsPair("examples/local/2019smtcomp/ABV", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
//			new DirectoryFileEndingsPair("examples/local/2019smtcomp/QF_UFBV", new String[]{ SMT_FILEENDING }, FILE_OFFSET, FILES_PER_DIRECTORY_LIMIT),
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

