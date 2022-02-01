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
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompOverflowTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class ErrorLocalizationSvcomp17Overflow extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
	// private static final int FILES_PER_DIR_LIMIT = 4;
	private static final int FILE_OFFSET = 0;

	private static final String STANDARD_DOT_C_PATTERN = ".*_false-no-overflow.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*_false-no-overflow.*\\.i";

	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS_32BIT = {
		/***** Category 4. Overflows *****/
		/*** Subcategory  Overflows-Other ***/
		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
	};
	// @formatter:on

	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS_64BIT = {
		/***** Category 4. Overflows *****/
		/*** Subcategory Overflows-BitVectors ***/
		new DirectoryFileEndingsPair("examples/svcomp/signedintegeroverflow-regression/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
			
		/***** Category 6. SoftwareSystems *****/
		/*** Subcategory  Systems_BusyBox_Overflows ***/
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT) ,
	};
	// @formatter:on

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompOverflowTestResultDecider(urd, false);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 300 * 1000;
	}

	/**
	 * List of path to setting files. Ultimate will run on each program with each setting that is defined here. The path
	 * are defined relative to the folder "trunk/examples/settings/", because we assume that all settings files are in
	 * this folder.
	 */
	private static final String[] SETTINGS_32BIT = {
		// @formatter:off
		"svcomp2017/automizer/svcomp-Overflow-32bit-Automizer_Default.epf",
		// @formatter:on
	};

	private static final String[] SETTINGS_64BIT = {
		// @formatter:off
		"svcomp2017/automizer/svcomp-Overflow-64bit-Automizer_Default.epf",
		// @formatter:on
	};

	private static final String[] TOOLCHAINS = {
		// @formatter:off
		"AutomizerCInline.xml",
		// @formatter:on
	};

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
