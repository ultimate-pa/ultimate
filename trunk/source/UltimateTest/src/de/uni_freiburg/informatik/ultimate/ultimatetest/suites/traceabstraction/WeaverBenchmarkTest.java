/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

public class WeaverBenchmarkTest extends AbstractTraceAbstractionTestSuite {
	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = 5;
	private static final int FILE_OFFSET = 0;

	private static final String STANDARD_DOT_BPL_PATTERN = ".*\\.bpl";

	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS = {
		/***** Category  *****/
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/bench/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/chl/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/parallel/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/popl20/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/popl20-bad/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/popl20-more/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/popl20-proofs/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/concurrent/bpl/weaver-benchmarks/generated/test/", new String[]{ STANDARD_DOT_BPL_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
	};


	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompReachTestResultDecider(urd, false);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 15_000;
	}

	/**
	 * List of setting files, path defined relative to the folder
	 * "trunk/examples/settings/",
	 */
	private static final String[] SETTINGS = {
//		"default/automizer/svcomp-Reach-32bit-Automizer_Default.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-NoLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-Sleep-NoLbe-New_States.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-SemanticLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-VariableLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-VariableLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Backfolding.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe-Backfolding.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Dbo.epf",
	};




	private static final String[] TOOLCHAINS = {
		"AutomizerBplInline.xml",
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), SETTINGS, toolchain, getTimeout(),
						dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCases();
	}
}
