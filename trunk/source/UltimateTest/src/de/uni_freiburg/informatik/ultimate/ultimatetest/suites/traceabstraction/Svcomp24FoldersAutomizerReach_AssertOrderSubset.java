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
public class Svcomp24FoldersAutomizerReach_AssertOrderSubset extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	// private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
	private static final int FILES_PER_DIR_LIMIT = 1000;
	private static final int FILE_OFFSET = 0;

	private static final String PROPERTY = TestUtil.SVCOMP_PROP_UNREACHCALL;
	private static final Boolean EXPECTED_RESULT = null;

	// @formatter:off
	private static final SvcompFolderSubset[] BENCHMARKS = {
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sum_by_3.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/mono-crafted_9.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/nested3-1_abstracted.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/nested_delay_nd.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/loopv2.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt5.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt7.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt9.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/nested3-1.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt6.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sum_by_3_abstracted.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt8.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/mono-crafted_12.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt4.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt2.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/nested3-2_abstracted.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/sumt3.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/nested5-1.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops-crafted-1/loopv1.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/verifythis/tree_del_rec_incorrect.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/verifythis/tree_del_iter_incorrect.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/verifythis/tree_del_iter.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/verifythis/tree_del_rec.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-zilu/benchmark09_conjunctive.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-simple/nested_3.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-simple/nested_4.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops/count_up_down-1.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loops/lu.cmp.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-new/count_by_1_variant.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-lit/mine2017-ex4.6.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-lit/hh2012-ex1b.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-lit/hh2012-ex2b.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-acceleration/nested_1-1.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-acceleration/array_1-2.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-acceleration/phases_2-2.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
			new SvcompFolderSubset("examples/svcomp/loop-invgen/large_const.yml", PROPERTY, EXPECTED_RESULT, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
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
		return 10 * 1000;
	}

	private static final Pair[] SETTINGS = {
//			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Default.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Default.epf"),
//			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf"),
//			new Pair<>("automizer/acceleratedInterpolation/acceleratedTraceCheck_32.epf", "automizer/acceleratedInterpolation/acceleratedTraceCheck_64.epf"),
//			new Pair<>("default/automizer/svcomp-Reach-32bit-Automizer_Default-FullInlining.epf", "default/automizer/svcomp-Reach-64bit-Automizer_Default-FullInlining.epf"),

			new Pair<>("automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation.epf","automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation.epf"),
			new Pair<>("automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-H1.epf","automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-H1.epf"),
			new Pair<>("automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-ShuffSing.epf","automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-ShuffSing.epf"),
			new Pair<>("automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-Dfg.epf","automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-Dfg.epf"),
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
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromSvcompYaml(dfep, SETTINGS, toolchain,
						getTimeout()));
			}
		}
		return super.createTestCases();
	}

}
