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
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompMemsafetyTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp17FoldersAutomizerMemsafety extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
	// private static final int FILES_PER_DIR_LIMIT = 1;
	private static final int FILE_OFFSET = 0;

	private static final String STANDARD_DOT_C_PATTERN = ".*_false-valid-deref.*\\.c|.*_false-valid-free.*\\.c|.*_false-valid-memtrack.*\\.c|.*_true-valid-memsafety.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*_false-valid-deref.*\\.i|.*_false-valid-free.*\\.c|.*_false-valid-memtrack.*\\.c|.*_true-valid-memsafety.*\\.i";

	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS_32BIT = {
		/***** Category 2. MemSafety *****/
		/*** Subcategory    MemSafety-Arrays ***/
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/reducercommutativity/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   MemSafety-Heap ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/bitvector-loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		
		/*** Subcategory    MemSafety-LinkedLists ***/
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/forester-heap/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		
		/*** Subcategory    MemSafety-Other ***/
		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
	};
	
	
	private static final DirectoryFileEndingsPair[] BENCHMARKS_64BIT = {
	};
	
	
	
	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompMemsafetyTestResultDecider(urd, false);
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
		"svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf",
		"svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf",
	};
	
	private static final String[] SETTINGS_64BIT = {
		"svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf",
		"svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Bitvector.epf",
	};
	


	
	
	private static final String[] TOOLCHAINS = {
		"AutomizerC.xml",
//		"AutomizerCInline.xml",
//		"AutomizerCInlineTransformed.xml",
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_32BIT) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), SETTINGS_32BIT, toolchain,
						getTimeout(), dfep.getOffset(), dfep.getLimit()));
			}
		}
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_64BIT) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), SETTINGS_64BIT, toolchain,
						getTimeout(), dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCases();
	}

}
