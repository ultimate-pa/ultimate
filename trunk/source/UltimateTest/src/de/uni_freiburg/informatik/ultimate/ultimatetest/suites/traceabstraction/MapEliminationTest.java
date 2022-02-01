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
import de.uni_freiburg.informatik.ultimate.test.decider.SomeVerificationResultTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class MapEliminationTest extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
	// private static final int FILES_PER_DIR_LIMIT = 5;
	private static final int FILE_OFFSET = 0;

	private static final String STANDARD_DOT_C_PATTERN = ".*_false-unreach-call.*\\.c|.*_true-unreach-call.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*_false-unreach-call.*\\.i|.*_true-unreach-call.*\\.i";

	private static final String BITVECTOR_FOLDER_DOT_C_PATTERN =
			".*_false-unreach-call.*\\.c|.*_true-unreach-call.*\\.c.cil.c";

	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS_32BIT = {
//		/***** Category 1. ReachSafety *****/
//		/*** Subcategory    ReachSafety-Arrays ***/
//		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/array-industry-pattern/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/reducercommutativity/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-BitVectors ***/
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ BITVECTOR_FOLDER_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector-loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-ControlFlow ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-ReachSafety-ECA ***/
//		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/psyco/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Heap ***/
//		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		// TODO: add ldv-regression/test[0-9][0-9]_false-unreach-call*.c ldv-regression/test[0-9][0-9]_true-unreach-call*.c
//		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/forester-heap/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/list-ext2-properties/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory    ReachSafety-Floats ***/
//		new DirectoryFileEndingsPair("examples/svcomp/floats-cdfpl/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/floats-cbmc-regression/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/float-benchs/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/floats-esbmc-regression/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Loops ***/
//		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-industry-pattern/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-ProductLines ***/
//		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Recursive ***/
//		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/recursive-simple/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Sequentialized ***/
//		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		
	};
	
	
	
	private static final DirectoryFileEndingsPair[] BENCHMARKS_64BIT = {
//		/***** Category 6. SoftwareSystems *****/
//		/*** Subcategory  Systems_DeviceDriversLinux64_ReachSafety ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.8/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.2-rc1/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-challenges/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.14/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.0-rc1-mav/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
	};
	
	
	private static final String[] ULTIMATE_REPO = {
			"examples/programs/regression",
//			"examples/programs/quantifier",
//			"examples/programs/recursive/regression",
//			"examples/programs/toy",
//			"examples/programs/20170304-DifficultPathPrograms",
//			"examples/ultimate-benchmarks/programs/20170329-DifficultLinuxPathPrograms/original",
//			"examples/ultimate-benchmarks/programs/20170412-SvcompReachPathPrograms/original",
//			"examples/ultimate-benchmarks/pathprograms/20170417-DifficultOverflow/",
//			"examples/ultimate-benchmarks/pathprograms/20170417-DifficultReach/",
		};
	
	
	
	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
//		return new SvcompReachTestResultDecider(urd, false);
		return new SomeVerificationResultTestResultDecider(urd);
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
	private static final String[] SETTINGS = {
		"automizer/Reach-64bit-Automizer-SingleStatement-Penguin.epf",
//		"automizer/DumpDifficultPathProgramsFromIcfg_svcomp-Reach-64bit-Automizer_MapElimination.epf",
//		"automizer/DumpDifficultPathProgramsFromIcfg_svcomp-Reach-64bit-Automizer_ModuloNeighbor.epf",
	};
	

	
	
	private static final String[] TOOLCHAINS_C = {
//		"AutomizerC.xml",
		"AutomizerCInline.xml",
		"AutomizerCInlineTransformedBlockencoded.xml",
	};
	
	private static final String[] TOOLCHAINS_BPL = {
//		"AutomizerBpl.xml",
		"AutomizerBplInline.xml",
		"AutomizerBplInlineTransformedBlockencoded.xml",
		};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_32BIT) {
			for (final String toolchain : TOOLCHAINS_C) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), SETTINGS, toolchain, getTimeout(),
						dfep.getOffset(), dfep.getLimit()));
			}
		}
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_64BIT) {
			for (final String toolchain : TOOLCHAINS_C) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), SETTINGS, toolchain, getTimeout(),
						dfep.getOffset(), dfep.getLimit()));
			}
		}
		for (final String setting : SETTINGS) {
			for (final String toolchain : TOOLCHAINS_C) {
				addTestCase(toolchain, setting, ULTIMATE_REPO, new String[] { ".c", ".i" });
			}
		}
		for (final String setting : SETTINGS) {
			for (final String toolchain : TOOLCHAINS_BPL) {
				addTestCase(toolchain, setting, ULTIMATE_REPO, new String[] { ".bpl" });
			}
		}
		return super.createTestCases();
	}

}
