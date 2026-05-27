/*
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ReqParser plug-in.
 *
 * The ULTIMATE ReqParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ReqParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReqParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReqParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReqParer plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.InitialTransition;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEAMinimization;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;

/**
 * Test Class for Pea Complement.
 *
 * @author Lena Funk
 */

@RunWith(JUnit4.class)
public class PEAMinimizationTest {

	ArrayList<PhaseEventAutomata> mTestAutomata;

	public PEAMinimizationTest() {
		mTestAutomata = new ArrayList<>();

		final PhaseEventAutomata responseDelayGlobally = createResponseDelayGloballyPea();

		mTestAutomata.add(responseDelayGlobally);
	}

	// constructs a PEA corresponding to pattern ResponseDelay Globally
	public static PhaseEventAutomata createResponseDelayGloballyPea() {
		final Map<String, String> variables = new HashMap<>();
		final CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		final CDD s = BooleanDecision.create("S");
		variables.put("S", "boolean");
		final CDD locInv0 = s.or(r.negate());
		final CDD locInv1 = r.and(s.negate());
		final CDD locInv2 = r.negate().and(s.negate());
		final CDD clkInv = RangeDecision.create("clk", RangeDecision.OP_LTEQ, 5);
		final CDD clkGuard = RangeDecision.create("clk", RangeDecision.OP_LT, 5);

		final List<String> clocks = new ArrayList<>();
		clocks.add("clk");

		final String[] reset = { "clk" };
		final String[] noreset = {};

		final Phase[] phases =
				{ new Phase("0", locInv0, CDD.TRUE), new Phase("1", locInv1, clkInv), new Phase("2", locInv2, clkInv) };

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], clkGuard, noreset);
		phases[2].addTransition(phases[2], clkGuard, noreset);

		// transitions
		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], s, noreset);
		phases[1].addTransition(phases[2], clkGuard, noreset);
		phases[2].addTransition(phases[1], clkGuard, noreset);
		phases[2].addTransition(phases[0], s, noreset);

		// initial transitions
		phases[0].setInitialTransition(new InitialTransition(CDD.TRUE, phases[0]));
		phases[1].setInitialTransition(new InitialTransition(CDD.TRUE, phases[1]));

		return new PhaseEventAutomata("ResponseDelayGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition(CDD.TRUE, phases[0]), new InitialTransition(CDD.TRUE, phases[1])),
				clocks, variables, Collections.emptyList());
	}

	@Test
	public void testPhasePartition() {
		final PhaseEventAutomata testPEA = mTestAutomata.get(0);
		final PEAMinimization minPea = new PEAMinimization(testPEA);
		final Map<CDD, Set<Phase>> partition = minPea.getPartitionByClockInv();
		final CDD clockInvCdd = RangeDecision.create("clk", RangeDecision.OP_LTEQ, 5);
		// final Set<Phase> set1 = partition.get(clockInvCdd);
		// assertEquals(set1.size(), 2);
		final Set<Phase> set2 = partition.get(CDD.TRUE);
		assertEquals(set2.size(), 2);

	}

	public void testMergable() {
		final PhaseEventAutomata testPEA = mTestAutomata.get(0);
		final PEAMinimization minPea = new PEAMinimization(testPEA);
		assert (minPea.isMergable(testPEA.getPhases().get(0), testPEA.getPhases().get(0)));
	}

	public void testMin() {
		final PhaseEventAutomata testPEA = mTestAutomata.get(0);
		final PEAMinimization minPea = new PEAMinimization(testPEA);
	}

}
