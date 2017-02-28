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

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp17FoldersAutomizerReach extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
//	private static final int FILES_PER_DIR_LIMIT = 1;
	private static final int FILE_OFFSET = 0;
	
	private static final String STANDARD_DOT_C_PATTERN = ".*_false-unreach-call.*\\.c|.*_true-unreach-call.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*_false-unreach-call.*\\.i|.*_true-unreach-call.*\\.i";
	
//	private static final String STANDARD_DOT_C_PATTERN = ".*_false-unreach-call.*\\.c";
//	private static final String STANDARD_DOT_I_PATTERN = ".*_false-unreach-call.*\\.i";

	
	
	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS_32BIT = {
		/***** Category 1. ReachSafety *****/
		/*** Subcategory   ReachSafety-Loops ***/
		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-industry-pattern/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
	};
	
	
	
	private static final DirectoryFileEndingsPair[] BENCHMARKS_64BIT = {
		/***** Category 6. SoftwareSystems *****/
		/*** Subcategory  Systems_DeviceDriversLinux64_ReachSafety ***/
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.8/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.2-rc1/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-challenges/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.14/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.0-rc1-mav/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT) ,
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
		return 60 * 1000;
	}

	/**
	 * List of setting files, path defined relative to the folder 
	 * "trunk/examples/settings/",
	 */
	private static final String[] SETTINGS_32BIT = {
		"svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Default.epf",
		"svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf",
	};
	
	private static final String[] SETTINGS_64BIT = {
//		"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf",
//		"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf",
	};
	


	
	
	private static final String[] TOOLCHAINS = {
		"AutomizerC.xml",
	};
	// @formatter:on

	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_32BIT) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[]{dfep.getDirectory()}, dfep.getFileEndings(), SETTINGS_32BIT, 
						toolchain, dfep.getOffset(), dfep.getLimit()));
			}
		}
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_64BIT) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[]{dfep.getDirectory()}, dfep.getFileEndings(), SETTINGS_64BIT, 
						toolchain, dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCases();
	}

	
}
