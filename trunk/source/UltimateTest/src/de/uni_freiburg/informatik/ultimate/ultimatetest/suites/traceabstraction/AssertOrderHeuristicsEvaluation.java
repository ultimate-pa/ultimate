/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;

/**
 * @author Betim Musa (musab@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class AssertOrderHeuristicsEvaluation extends AbstractTraceAbstractionTestSuite {

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new SafetyCheckTestResultDecider(ultimateRunDefinition, false);
	}

	// @formatter:off

	private static final String[] mUltimateRepository = {
//			"examples/programs/nonlinearArithmetic",
//			"examples/programs/quantifier",
//			"examples/programs/random",
//			"examples/programs/real-life",
//			"examples/programs/reals",
//			"examples/programs/recursive/regression",
//			"examples/programs/regression",
//			"examples/programs/scalable",
//			"examples/programs/toy",
//			"examples/programs/toy/tooDifficultLoopInvariant/",
//			"examples/programs/20170304-DifficultPathPrograms/",
//			"examples/programs/20170319-ConjunctivePathPrograms",
//			"examples/programs/20181010-MemSafetyPathprograms",
//			"examples/programs/20181015-LoopsPathprograms/",

			/* List of benchmarks were we were successful with at least one assert order but were we were not successful with at least one assert order  */
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/afnp2014.c.i_3.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/cggmp2005b.c.i_4.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/count_by_1.i_3.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/count_by_1_variant.i_2.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/count_up_down.i_3.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/eureka_01.i_6.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/gauss_sum.i_3.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/gcd_2.i_4.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/gj2007.c.i_4.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/gr2006.c.i_4.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/invert_string.i_4.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/jain_2.i_2.bpl",
			"examples/programs/20170304-DifficultPathPrograms/resultKnown/phases1.i_3.bpl",
			"examples/programs/20170319-ConjunctivePathPrograms/resultKnown/count_by_1_variant.i_2.bplTransformedIcfg_BEv2_3.bpl",
			"examples/programs/20170319-ConjunctivePathPrograms/resultKnown/count_up_down.i_3.bplTransformedIcfg_BEv2_7.bpl",
			"examples/programs/20170319-ConjunctivePathPrograms/resultKnown/count_up_down.i_3.bplTransformedIcfg_BEv2_7.bpl",
			"examples/programs/20170319-ConjunctivePathPrograms/resultKnown/gauss_sum.i_3.bplTransformedIcfg_BEv2_3.bpl",
			"examples/programs/20170319-ConjunctivePathPrograms/resultKnown/gj2007.c.i_4.bplTransformedIcfg_BEv2_3.bpl",
			"examples/programs/20170319-ConjunctivePathPrograms/resultKnown/gr2006.c.i_4.bplTransformedIcfg_BEv2_3.bpl",
			"examples/programs/20170319-ConjunctivePathPrograms/resultKnown/jain_5.i_2.bplTransformedIcfg_BEv2_4.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/20051113-1.c.i_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/20051113-1.c.i_17.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/20051113-1.c.i_46.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/20051113-1.c.i_5.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/20051113-1.c.i_7.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/20051113-1.c.i_9.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/960521-1.i_5.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/960521-1_1.i_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength.c_10.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength.c_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength.c_12.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength.c_13.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength2.c_16.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength2.c_18.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength2.c_19.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength5.c_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength5.c_12.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysOfVariableLength5.c_13.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysWithLenghtAtDeclaration-read.c_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysWithLenghtAtDeclaration-read.c_13.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysWithLenghtAtDeclaration.c_10.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysWithLenghtAtDeclaration.c_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/ArraysWithLenghtAtDeclaration.c_9.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/alternating_list.i_48.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/array3.i_5.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/array3.i_6.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/array3.i_8.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/count_down-alloca.i_8.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/memset.c_4.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/memset3.c_4.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/memsetNonZero.c_4.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/memsetNonZero3.c_4.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/sll-buckets.i_35.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/sll-buckets.i_41.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/sll-buckets.i_44.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/sll-buckets.i_45.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/standard_strcpy_ground.i_10.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/standard_strcpy_original.i_9.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/test-bitfields-2.1.i_17.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/test-bitfields-2.i_19.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/test-bitfields-2.i_21.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/test-bitfields-3.1.i_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/test-bitfields-3.i_11.bpl",
			"examples/programs/20181010-MemSafetyPathprograms/resultKnown/test-memleak_nexttime.i_16.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/cggmp2005b.c.i_4.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/count_by_1.i_3.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/count_by_1_variant.i_2.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/count_up_down.i_3.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/diamond1.i_3.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/gauss_sum.i_3.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/gj2007.c.i_4.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/gr2006.c.i_4.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/nested.c_4.bpl",
			"examples/programs/20181015-LoopsPathprograms/resultKnown/phases1.i_3.bpl",
			"examples/programs/toy/InterpolantConsolidation02.bpl",
			"examples/programs/toy/InvariantChecking/showcase/ArrayInitialization02.bpl",
			"examples/programs/toy/InvariantChecking/showcase/MultiplicationOfNaturalNumbers.bpl",
			"examples/programs/toy/UselessIncrement.bpl",
			"examples/programs/toy/multiply.c",
			"examples/programs/toy/nonlinear/ConstantValue-Safe.bpl",
			"examples/programs/toy/nonlinear/InterpolationPaperExampleCandidate01.bpl",
			"examples/programs/toy/nonlinear/NonlinearInvariant1-Safe.bpl",
			"examples/programs/toy/nonlinear/PositiveValue-Safe.bpl",
			"examples/programs/toy/nonlinear/Power1-Safe.bpl",
			"examples/programs/toy/nonlinear/Power2-Unsafe.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/2006CAV-GopanReps-Fig1.c",
			"examples/programs/toy/tooDifficultLoopInvariant/2007POPL-GulwaniJojic-Figure3.c",
			"examples/programs/toy/tooDifficultLoopInvariant/2007POPL-GulwaniJojic-Figure3.c",
			"examples/programs/toy/tooDifficultLoopInvariant/2007POPL-GulwaniJojic-Figure3.c",
			"examples/programs/toy/tooDifficultLoopInvariant/2007POPL-GulwaniJojic-Figure3.c",
			"examples/programs/toy/tooDifficultLoopInvariant/2007POPL-GulwaniJojic-Figure3.c",
			"examples/programs/toy/tooDifficultLoopInvariant/ArrayInit01.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/ArrayInit02.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/BeyerHenzingerMajumdarRybalchenko-PLDI2007-Figure4.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/CountTillBound-Jupiter.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/DrAlban01-easy.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/DrAlban02-medium.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/LargeConstant-ForwardSuccess.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/MirabelleConcurrentIncrementNondetSeq.bpl",
			"examples/programs/toy/tooDifficultLoopInvariant/OrderDependentEquality.c",

	};


	/**
	 * List of path to setting files.
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 *
	 */
	private static final String[] mSettings = {
//		/*** No Heuristic ***/
//		"automizer/AssertOrderHeuristics/Reach-32bit-CVC4-IcSpLv-Bitvector.epf",
//		/*** Heuristic 1 (OUTSIDE_LOOP_FIRST1) ***/
//		"automizer/AssertOrderHeuristics/Reach-32bit-CVC4-IcSpLv-Bitvector-H1.epf",
//		/*** Heuristic 2 (OUTSIDE_LOOP_FIRST2) ***/
//		"automizer/AssertOrderHeuristics/Reach-32bit-CVC4-IcSpLv-Bitvector-H2.epf",
//		/*** Heuristic 3 (INSIDE_LOOP_FIRST1) ***/
//		"automizer/AssertOrderHeuristics/Reach-32bit-CVC4-IcSpLv-Bitvector-H3.epf",
//		/*** Heuristic 4 (MIX_INSIDE_OUTSIDE) ***/
//		"automizer/AssertOrderHeuristics/Reach-32bit-CVC4-IcSpLv-Bitvector-H4.epf",
//		/*** Heuristic 5 (TERMS_WITH_SMALL_CONSTANTS_FIRST) ***/
//		"automizer/AssertOrderHeuristics/Reach-32bit-CVC4-IcSpLv-Bitvector-H5.epf",

		/*** No Heuristic ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcSpLv.epf",
		/*** Heuristic 1 (OUTSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcSpLv-H1.epf",
		/*** Heuristic 2 (OUTSIDE_LOOP_FIRST2) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcSpLv-H2.epf",
		/*** Heuristic 3 (INSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcSpLv-H3.epf",
		/*** Heuristic 4 (MIX_INSIDE_OUTSIDE) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcSpLv-H4.epf",
		/*** Heuristic 5 (TERMS_WITH_SMALL_CONSTANTS_FIRST) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcSpLv-H5.epf",

		/*** No Heuristic ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcWpLv.epf",
		/*** Heuristic 1 (OUTSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcWpLv-H1.epf",
		/*** Heuristic 2 (OUTSIDE_LOOP_FIRST2) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcWpLv-H2.epf",
		/*** Heuristic 3 (INSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcWpLv-H3.epf",
		/*** Heuristic 4 (MIX_INSIDE_OUTSIDE) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcWpLv-H4.epf",
		/*** Heuristic 5 (TERMS_WITH_SMALL_CONSTANTS_FIRST) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-IcWpLv-H5.epf",

		/*** No Heuristic ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-NestedInterpolation.epf",
		/*** Heuristic 1 (OUTSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-NestedInterpolation-H1.epf",
		/*** Heuristic 2 (OUTSIDE_LOOP_FIRST2) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-NestedInterpolation-H2.epf",
		/*** Heuristic 3 (INSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-NestedInterpolation-H3.epf",
		/*** Heuristic 4 (MIX_INSIDE_OUTSIDE) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-NestedInterpolation-H4.epf",
		/*** Heuristic 5 (TERMS_WITH_SMALL_CONSTANTS_FIRST) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-NestedInterpolation-H5.epf",

		/*** No Heuristic ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation.epf",
		/*** Heuristic 1 (OUTSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-H1.epf",
		/*** Heuristic 2 (OUTSIDE_LOOP_FIRST2) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-H2.epf",
		/*** Heuristic 3 (INSIDE_LOOP_FIRST1) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-H3.epf",
		/*** Heuristic 4 (MIX_INSIDE_OUTSIDE) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-H4.epf",
		/*** Heuristic 5 (TERMS_WITH_SMALL_CONSTANTS_FIRST) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-H5.epf",
		/*** Heuristic 6 (SHUFFLED_SINGLETONS) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-ShuffSing.epf",
		/*** Heuristic 7 (DFG_BASED) ***/
		"automizer/AssertOrderHeuristics/Reach-32bit-Automizer_Default-TreeInterpolation-Dfg.epf",
	};
	// @formatter:on

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 20 * 1000;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		for (final String setting : mSettings) {
			addTestCase("AutomizerBpl.xml", setting, mUltimateRepository, new String[] { ".bpl" });
		}
		for (final String setting : mSettings) {
			addTestCase("AutomizerC.xml", setting, mUltimateRepository, new String[] { ".c", ".i" });
		}
		return super.createTestCases();
	}

}
