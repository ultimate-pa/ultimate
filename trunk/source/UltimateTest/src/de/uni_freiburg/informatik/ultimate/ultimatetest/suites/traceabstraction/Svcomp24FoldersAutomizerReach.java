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
	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
	//private static final int FILES_PER_DIR_LIMIT = 3;
	private static final int FILE_OFFSET = 0;

	private static final String PROPERTY = TestUtil.SVCOMP_PROP_UNREACHCALL;
	private static final Boolean EXPECTED_RESULT = null;

	// @formatter:off
	private static final SvcompFolderSubset[] BENCHMARKS = {
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/array-crafted/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/array-examples/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/array-memsafety-realloc/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/bitvector/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/bitvector-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/busybox-1.22.0/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/combinations/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/float-benchs/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/float-newlib/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/floats-cbmc-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/floats-cdfpl/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/floats-esbmc-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/forester-heap/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/goblint-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/hardness-nfm22/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/hardware-verification-bv/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-challenges/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-commit-tester/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-consumption/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-linux-3.0/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-linux-3.4-simple/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-linux-3.7.3/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-linux-3.12-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-linux-3.16-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-linux-4.0-rc1-mav/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-linux-4.2-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-races/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-validator-v0.6/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ldv-validator-v0.8/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/list-ext3-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/list-ext-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/list-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/locks/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/longjmp/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/loop-floats-scientific-comp/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/loop-invariants/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/loops/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/memsafety/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/memsafety-bftpd/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/neural-networks/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/nla-digbench/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/nla-digbench-scaling/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/ntdrivers/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/product-lines/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread-atomic/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread-C-DAC/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread-deagle/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread-ext/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread-lit/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread-memsafety/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/pthread-wmm/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/recursified_loop-invariants/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/recursified_nla-digbench/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/termination-recursive-malloc/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp_overapprox_only_unsafe/weaver/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

		
		
//		new SvcompFolderSubset("examples/svcomp_overapprox/array-crafted/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/array-examples/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/array-memsafety-realloc/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/bitvector/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/bitvector-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/busybox-1.22.0/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/combinations/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/float-benchs/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/float-newlib/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/floats-cbmc-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/floats-cdfpl/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/floats-esbmc-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/forester-heap/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/goblint-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/hardness-nfm22/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/hardware-verification-bv/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-challenges/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-commit-tester/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-consumption/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-linux-3.0/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-linux-3.4-simple/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-linux-3.7.3/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-linux-3.12-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-linux-3.16-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-linux-4.0-rc1-mav/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-linux-4.2-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-races/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-validator-v0.6/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ldv-validator-v0.8/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/list-ext3-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/list-ext-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/list-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/locks/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/longjmp/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/loop-floats-scientific-comp/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/loop-invariants/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/loops/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/memsafety/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/memsafety-bftpd/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/neural-networks/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/nla-digbench/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/nla-digbench-scaling/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/ntdrivers/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/product-lines/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread-atomic/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread-C-DAC/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread-deagle/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread-ext/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread-lit/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread-memsafety/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/pthread-wmm/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/recursified_loop-invariants/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/recursified_nla-digbench/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/termination-recursive-malloc/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp_overapprox/weaver/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		
		
		/***** Category 1. ReachSafety *****/
		/*** Subcategory    ReachSafety-Arrays ***/
//		new SvcompFolderSubset("examples/svcomp/array-examples/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-industry-pattern/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/reducercommutativity/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-tiling/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-programs/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-crafted/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-multidimensional/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-patterns/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-cav19/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-lopstr16/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/array-fpi/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-BitVectors ***/
//		new SvcompFolderSubset("examples/svcomp/bitvector/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/bitvector-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/bitvector-loops/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Combinations ***/
//		new SvcompFolderSubset("examples/svcomp/combinations/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-ControlFlow ***/
//		new SvcompFolderSubset("examples/svcomp/ntdrivers-simplified/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/openssl-simplified/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/locks/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ntdrivers/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/openssl/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/memory-model/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/unsignedintegeroverflow-sas23/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/longjmp/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-ReachSafety-ECA ***/
//		new SvcompFolderSubset("examples/svcomp/eca-rers2012/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/eca-rers2018/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/psyco/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/eca-programs/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory    ReachSafety-Floats ***/
//		new SvcompFolderSubset("examples/svcomp/floats-cdfpl/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/floats-cbmc-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/float-benchs/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/floats-esbmc-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/float-newlib/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-floats-scientific-comp/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/neural-networks/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ??? ***/
//		new SvcompFolderSubset("examples/svcomp/fuzzle-programs/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ??? ***/
//		new SvcompFolderSubset("examples/svcomp/hardness-nfm22/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Hardware.set ***/
//		new SvcompFolderSubset("examples/svcomp/hardware-verification-array/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/hardware-verification-bv/", PROPERTY, true, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Heap ***/
//		new SvcompFolderSubset("examples/svcomp/heap-manipulation/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/list-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-regression/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ddv-machzwd/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/forester-heap/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/list-ext-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/list-ext2-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-sets/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/list-simple/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/heap-data/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/list-ext3-properties/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Loops ***/
//		new SvcompFolderSubset("examples/svcomp/loops/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-acceleration/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-invgen/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-lit/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-new/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-industry-pattern/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loops-crafted-1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-invariants/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-simple/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/loop-zilu/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/verifythis/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/nla-digbench/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/nla-digbench-scaling/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-ProductLines ***/
//		new SvcompFolderSubset("examples/svcomp/product-lines/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Recursive ***/
//		new SvcompFolderSubset("examples/svcomp/recursive/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/recursive-simple/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/recursive-with-pointer/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/recursified_loop-crafted/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/recursified_loop-invariants/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/recursified_loop-simple/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/recursified_nla-digbench/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Sequentialized ***/
//		new SvcompFolderSubset("examples/svcomp/systemc/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/seq-mthreaded/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/seq-mthreaded-reduced/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/seq-pthread/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-XCSP ***/
//		new SvcompFolderSubset("examples/svcomp/xcsp/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/***** Category 6. SoftwareSystems *****/
//		new SvcompFolderSubset("examples/svcomp/aws-c-common/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		new SvcompFolderSubset("examples/svcomp/busybox-1.22.0/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		new SvcompFolderSubset("examples/svcomp/goblint-coreutils/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory  Systems_DeviceDriversLinux64_ReachSafety ***/
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.0/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.4-simple/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.7.3/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-commit-tester/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-consumption/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.12-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.16-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-validator-v0.6/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-validator-v0.8/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-4.2-rc1/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.14/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-challenges/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new SvcompFolderSubset("examples/svcomp/ldv-linux-4.0-rc1-mav/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		new SvcompFolderSubset("examples/svcomp/uthash-2.0.2/", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

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
		return 60 * 1000;
	}

	private static final Pair[] SETTINGS = {
			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Default_IcfgBuilder.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Default_IcfgBuilder.epf"),
			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Bitvector_IcfgBuilder.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Bitvector_IcfgBuilder.epf"),
//			
//			new Pair<>("default/automizer/svcomp-Termination-32bit-Automizer_Default_IcfgBuilder.epf", "default/automizer/svcomp-Termination-64bit-Automizer_Default_IcfgBuilder.epf"),
//			
//			new Pair<>("default/automizer/svcomp-Overflow-32bit-Automizer_Default_IcfgBuilder.epf", "default/automizer/svcomp-Overflow-64bit-Automizer_Default_IcfgBuilder.epf"),
//			new Pair<>("default/automizer/svcomp-Overflow-32bit-Automizer_Bitvector_IcfgBuilder.epf", "default/automizer/svcomp-Overflow-64bit-Automizer_Bitvector_IcfgBuilder.epf"),
//			
//			new Pair<>("default/automizer/svcomp-MemCleanup-32bit-Automizer_Default_IcfgBuilder.epf", "default/automizer/svcomp-MemCleanup-64bit-Automizer_Default_IcfgBuilder.epf"),
//			new Pair<>("default/automizer/svcomp-MemCleanup-32bit-Automizer_Bitvector_IcfgBuilder.epf", "default/automizer/svcomp-MemCleanup-64bit-Automizer_Bitvector_IcfgBuilder.epf"),
//			
//			new Pair<>("default/automizer/svcomp-LTL-32bit-Automizer_Default.epf", "default/automizer/svcomp-LTL-64bit-Automizer_Default.epf"),
//			
//			new Pair<>("default/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default_IcfgBuilder.epf", "default/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default_IcfgBuilder.epf"),
//			new Pair<>("default/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector_IcfgBuilder.epf", "default/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Bitvector_IcfgBuilder.epf"),
//			
//			new Pair<>("default/automizer/svcomp-DataRace-32bit-Automizer_Default.epf", "default/automizer/svcomp-DataRace-64bit-Automizer_Default.epf"),
//			new Pair<>("default/automizer/svcomp-DataRace-32bit-Automizer_Bitvector.epf", "default/automizer/svcomp-DataRace-64bit-Automizer_Bitvector.epf")
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
				try {
					addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromSvcompYaml(dfep, SETTINGS,
							toolchain, getTimeout()));
				} catch (Exception e) {
					// TODO: handle exception
				}

			}
		}
		return super.createTestCases();
	}

}
