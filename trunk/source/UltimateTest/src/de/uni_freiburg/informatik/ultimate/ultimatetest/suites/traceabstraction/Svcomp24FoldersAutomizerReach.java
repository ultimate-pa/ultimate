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
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompTestResultDeciderUnreachCall;
import de.uni_freiburg.informatik.ultimate.test.util.SvcompFolderSubset;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Svcomp24FoldersAutomizerReach extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
//	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
	 private static final int FILES_PER_DIR_LIMIT = 10;
	private static final int FILE_OFFSET = 0;

	private static final String PROPERTY = TestUtil.SVCOMP_PROP_UNREACHCALL;

	// @formatter:off
	private static final SvcompFolderSubset[] BENCHMARKS = {
		/***** Category 1. ReachSafety *****/
		/*** Subcategory    ReachSafety-Arrays ***/
		new SvcompFolderSubset("examples/svcomp/array-examples/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-industry-pattern/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/reducercommutativity/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-tiling/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-programs/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-crafted/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-multidimensional/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-patterns/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-cav19/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-lopstr16/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/array-fpi/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-BitVectors ***/
		new SvcompFolderSubset("examples/svcomp/bitvector/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/bitvector-regression/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/bitvector-loops/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-Combinations ***/
		new SvcompFolderSubset("examples/svcomp/combinations/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-ControlFlow ***/
		new SvcompFolderSubset("examples/svcomp/ntdrivers-simplified/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/openssl-simplified/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/locks/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ntdrivers/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/openssl/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/memory-model/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/unsignedintegeroverflow-sas23/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/longjmp/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-ReachSafety-ECA ***/
		new SvcompFolderSubset("examples/svcomp/eca-rers2012/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/eca-rers2018/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/psyco/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/eca-programs/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory    ReachSafety-Floats ***/
		new SvcompFolderSubset("examples/svcomp/floats-cdfpl/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/floats-cbmc-regression/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/float-benchs/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/floats-esbmc-regression/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/float-newlib/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-floats-scientific-comp/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/neural-networks/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ??? ***/
		new SvcompFolderSubset("examples/svcomp/fuzzle-programs/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ??? ***/
		new SvcompFolderSubset("examples/svcomp/hardness-nfm22/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-Hardware.set ***/
		new SvcompFolderSubset("examples/svcomp/hardware-verification-array/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/hardware-verification-bv/", PROPERTY, true, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-Heap ***/
		new SvcompFolderSubset("examples/svcomp/heap-manipulation/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/list-properties/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-regression/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ddv-machzwd/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/forester-heap/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/list-ext-properties/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/list-ext2-properties/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-sets/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/list-simple/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/heap-data/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/list-ext3-properties/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-Loops ***/
		new SvcompFolderSubset("examples/svcomp/loops/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-acceleration/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-invgen/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-lit/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-new/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-industry-pattern/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loops-crafted-1/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-invariants/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-simple/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/loop-zilu/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/verifythis/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/nla-digbench/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/nla-digbench-scaling/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-ProductLines ***/
		new SvcompFolderSubset("examples/svcomp/product-lines/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-Recursive ***/
		new SvcompFolderSubset("examples/svcomp/recursive/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/recursive-simple/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/recursive-with-pointer/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/recursified_loop-crafted/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/recursified_loop-invariants/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/recursified_loop-simple/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/recursified_nla-digbench/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-Sequentialized ***/
		new SvcompFolderSubset("examples/svcomp/systemc/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/seq-mthreaded/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/seq-mthreaded-reduced/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/seq-pthread/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory   ReachSafety-XCSP ***/
		new SvcompFolderSubset("examples/svcomp/xcsp/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/***** Category 6. SoftwareSystems *****/
		new SvcompFolderSubset("examples/svcomp/aws-c-common/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		new SvcompFolderSubset("examples/svcomp/busybox-1.22.0/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		new SvcompFolderSubset("examples/svcomp/goblint-coreutils/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		/*** Subcategory  Systems_DeviceDriversLinux64_ReachSafety ***/
		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.0/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.4-simple/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.7.3/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-commit-tester/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-consumption/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.12-rc1/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.16-rc1/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-validator-v0.6/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-validator-v0.8/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-4.2-rc1/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.14/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-challenges/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-4.0-rc1-mav/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		new SvcompFolderSubset("examples/svcomp/uthash-2.0.2/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

	};

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompTestResultDeciderUnreachCall(urd, false);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 20 * 1000;
	}

	private static final Pair[] SETTINGS = {
			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Default.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Default.epf"),
			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf"),
//			new Pair<>("automizer/acceleratedInterpolation/acceleratedTraceCheck_32.epf", "automizer/acceleratedInterpolation/acceleratedTraceCheck_64.epf"),
//			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Default-FullInlining.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Default-FullInlining.epf"),
	};


	private static final String[] TOOLCHAINS = {
//		"AutomizerC.xml",
		"AutomizerCInline.xml",
//		"AutomizerCInlineTransformed.xml",
//		"AutomizerCInlineBlockencodedTransformed.xml"
//		"AutomizerCInline_WitnessPrinter.xml"
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final SvcompFolderSubset dfep : BENCHMARKS) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromSvcompYaml(dfep, SETTINGS,
						toolchain, getTimeout()));
			}
		}
		return super.createTestCases();
	}

}
