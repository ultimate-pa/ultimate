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
public class Svcomp19FoldersBitfieldsMemsafety extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = 20000;
	// private static final int FILES_PER_DIR_LIMIT = 1;
	private static final int FILE_OFFSET = 0;

	private static final String STANDARD_DOT_C_PATTERN = ".*_false-valid-deref.*\\.c|.*_false-valid-free.*\\.c|.*_false-valid-memtrack.*\\.c|.*_true-valid-memsafety.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*_false-valid-deref.*\\.i|.*_false-valid-free.*\\.c|.*_false-valid-memtrack.*\\.c|.*_true-valid-memsafety.*\\.i";


	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS_32BIT = {
		/***** Category  *****/
		new DirectoryFileEndingsPair("examples/svcomp/array-examples/relax_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-examples/relax_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety-realloc/array-realloc_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety-realloc/array-realloc_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/add_last-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/add_last_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/array01-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/array02-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/array03-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/bubblesort-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/count_down-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/count_down_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrcat-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrchr-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrchr_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrcmp-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrcpy-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrcspn-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrlen-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrlen_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrncat-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrncmp-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrncpy-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrpbrk-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrpbrk_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/cstrspn-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/diff-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/insertionsort-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/java_BubbleSort-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/knapsack_alloca_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/lis-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/lis_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/mult_array-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/mult_array_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cbzero-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cmemchr-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cmemrchr-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cmemset-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstpcpy-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstpncpy-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrcat-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrcmp-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrcpy-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrcspn-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrlcpy-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrlen-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrncat-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrncmp-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrncpy-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrnlen-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrpbrk-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrspn-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/openbsd_cstrstr-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/rec_strlen-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/reverse_array_alloca_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/reverse_array_unsafe_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/selectionsort-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/stroeder1-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/stroeder2-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/strreplace-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/subseq-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/substring-alloca_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/basename_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/basename_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/chgrp-incomplete_true-no-overflow_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/chroot-incomplete_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/cut_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/date_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/dirname_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/du_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/echo_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/expand_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/fold_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/head_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/head_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/hostid_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/logname_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/ls-incomplete_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/mkdir_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/mkfifo-incomplete_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/od_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/printf_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/readlink_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/realpath_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/rm_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/seq_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/sleep_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/sleep_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/stty_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/sync_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/tac_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/tee_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/test-incomplete_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/touch_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/uname_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/uniq_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/usleep_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/uudecode_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/wc_false-unreach-call_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/who_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/whoami-incomplete_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/yes_true-no-overflow_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_all_false-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_inb_p_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_inb_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_inl_p_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_inl_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_inw_false-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_inw_p_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_outb_false-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_outb_p_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_outl_p_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_outl_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_outw_p_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/ddv_machzwd_pthread_mutex_unlock_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/bubble_sort_linux_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/dancing_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/merge_sort_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/tree_false-unreach-call_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/tree_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-1_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-2.1_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-2.1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-2_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-2_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3.1_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3.1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test10_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test10_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test11_1_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test11_2_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test11_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test12_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test12_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test13_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test13_2_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test13_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test14_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test14_2_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test14_3_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test14_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test15_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test15_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test16_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test16_2_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test16_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test17_1_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test17_1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test17_2_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test17_2_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test17_3_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test18_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test18_2_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test18_3_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test18_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test19_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test19_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test1_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test20_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test20_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test21_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test21_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_2_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_2_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_3_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_3_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_4_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test22_5_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test23_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test23_2_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test23_4_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test3_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test3_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test4_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test4_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test5_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test5_2_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test5_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test6_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test6_2_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test6_3_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test6_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test7_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test7_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test8_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test8_2_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test8_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test9_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test9_2_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/memleaks_test9_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/960521-1_1_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/960521-1_1_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/960521-1_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/list-ext_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/list-ext_false-unreach-call_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/list-ext_flag_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/simple-ext_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0019_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0019_1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0158_1_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0158_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0158_1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0214_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0217_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0232_1_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0232_1_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0504_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/test-0513_1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/dll_circular_traversal_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/dll_circular_traversal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/dll_nondet_free_order_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/dll_nondet_free_order_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/dll_nullified_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/sll_circular_traversal_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/sll_circular_traversal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/sll_length_check_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/sll_nondet_insert_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/sll_of_sll_nondet_append_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/sll_shallow_copy_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-ext3-properties/sll_shallow_copy_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/alternating_list_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/list_flag_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/list_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/simple_built_from_end_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/simple_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/splice_true-unreach-call_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_append_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_append_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_insert_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_insert_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_prepend_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_prepend_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_remove_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_remove_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_update_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2c_update_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_append_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_append_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_insert_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_insert_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_prepend_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_prepend_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_remove_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_remove_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_update_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/dll2n_update_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_append_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_append_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_insert_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_insert_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_prepend_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_prepend_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_remove_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_remove_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_update_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2c_update_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_append_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_append_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_insert_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_insert_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_prepend_equal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_prepend_unequal_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_remove_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_remove_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_update_all_reverse_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/list-simple/sll2n_update_all_true-unreach-call_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/c.03-alloca_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/dll_extends_pointer_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/skiplist_2lvl_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/skiplist_3lvl_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/tree_cnstr_true-valid-memsafety_false-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/tree_dsw_true-valid-memsafety_false-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/tree_of_cslls_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/tree_parent_ptr_true-valid-memsafety_false-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/tree_stack_true-valid-memsafety_false-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/20020406-1_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/20051113-1.c_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/960521-1_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/960521-1_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/960521-1_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/lockfree-3.0_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/lockfree-3.1_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/lockfree-3.2_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/lockfree-3.3_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0019_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0019_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0102_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0102_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0134_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0137_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0158_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0158_false-valid-memtrack_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0158_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0214_true-valid-memsafety_false-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0217_true-valid-memsafety_false-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0218_true-valid-memsafety_false-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0219_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0220_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0232_false-valid-free.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0232_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0232_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0234_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0234_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0235_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0235_false-valid-memtrack.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0235_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0236_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0237_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0504_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0513_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-0521_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/test-memleak_nexttime_true-valid-memsafety_true-termination.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/floppy_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/kbfiltr_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/pthread-memsafety/fillarray_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/pthread-memsafety/fillarray_true-valid-memsafety.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/pthread-memsafety/list1_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/pthread-memsafety/list2_false-valid-deref.i", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

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
		return 20 * 1000;
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
