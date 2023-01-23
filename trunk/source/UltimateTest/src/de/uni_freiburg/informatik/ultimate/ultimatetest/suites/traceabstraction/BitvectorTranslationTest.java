/*
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
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ThreeTierTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * Test for translations from bitvectors to ints.
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class BitvectorTranslationTest extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
//	private static final int FILES_PER_DIR_LIMIT = 10;
	private static final int FILE_OFFSET = 0;

	private static final String STANDARD_DOT_C_PATTERN = ".*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*\\.i";
	private static final String MIXED = ".*\\.c";

	private static final DirectoryFileEndingsPair[] BENCHMARKS_32BIT = {
			/*** Subcategory   ReachSafety-BitVectors ***/
			new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ MIXED }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/bitvector-loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

			/*** Subcategory   ReachSafety-ControlFlow ***/
			new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/openssl-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/openssl/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

			/*** Subcategory   ReachSafety-Loops ***/
			new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-industry-pattern/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loops-crafted-1/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-invariants/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-simple/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-zilu/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/verifythis/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/nla-digbench/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/nla-digbench-scaling/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

			/*** Programs were we saw bugs ***/
			new DirectoryFileEndingsPair("examples/svcomp/bitvector/parity.c", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/bitvector/soft_float_4-2a.c.cil.c", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new DirectoryFileEndingsPair("examples/svcomp/loop-invariants/bin-suffix-5.c", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
	};

	private static final String[] mUltimateRepository = {
			"examples/programs/bitvector",
			"examples/programs/regression",
			"examples/programs/quantifier/regression",
			"examples/programs/recursive/regression",
//			"examples/programs/toy",
		};


	private static final String[] mSettingsNoTransformation = {
			"automizer/BvToInt/svcomp-Reach-32bit-Automizer_Default.epf",
			"automizer/BvToInt/svcomp-Reach-32bit-Automizer_Bitvector.epf",
	};

	private static final String[] mSettingsTransformation = {
			"automizer/BvToInt/svcomp-Reach-32bit-Automizer_BvToInt_SUM.epf",
			"automizer/BvToInt/svcomp-Reach-32bit-Automizer_BvToInt_BITWISE.epf",
			"automizer/BvToInt/svcomp-Reach-32bit-Automizer_BvToInt_LAZY.epf",
			"automizer/BvToInt/svcomp-Reach-32bit-Automizer_BvToInt_NONE.epf",
			"automizer/BvToInt/svcomp-Reach-32bit-Automizer_BvToIntCongruence_NONE.epf",
	};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 30 * 1000;
	}

	@Override
	protected ThreeTierTestResultDecider<?> constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompReachTestResultDecider(urd, true);
//		return new SafetyCheckTestResultDecider(urd, true);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_32BIT) {
			addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
					new String[] { dfep.getDirectory() }, dfep.getFileEndings(), mSettingsNoTransformation,
					"AutomizerCInline.xml", getTimeout(), dfep.getOffset(), dfep.getLimit()));
		}
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS_32BIT) {
			addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
					new String[] { dfep.getDirectory() }, dfep.getFileEndings(), mSettingsTransformation,
					"AutomizerCInlineTransformed.xml", getTimeout(), dfep.getOffset(), dfep.getLimit()));
		}
		for (final String setting : mSettingsNoTransformation) {
			addTestCase("AutomizerCInline.xml", setting, mUltimateRepository,
					new String[] {".c", ".i"});
		}

		for (final String setting : mSettingsTransformation) {
			addTestCase("AutomizerCInlineTransformed.xml", setting, mUltimateRepository,
					new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}


}
