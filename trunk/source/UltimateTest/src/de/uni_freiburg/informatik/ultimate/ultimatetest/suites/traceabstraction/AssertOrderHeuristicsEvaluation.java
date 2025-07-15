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
//		"examples/programs/nonlinearArithmetic",
//		"examples/programs/quantifier",
//		"examples/programs/random",
//		"examples/programs/real-life",
//		"examples/programs/reals",
		"examples/programs/recursive/regression",
		"examples/programs/regression",
//		"examples/programs/scalable",
//		"examples/programs/toy",
//		"examples/programs/toy/tooDifficultLoopInvariant/",
//		"examples/programs/20170304-DifficultPathPrograms/",
//		"examples/programs/20181015-LoopsPathprograms/",
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
		return 10 * 1000;
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
