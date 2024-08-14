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
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.InitialTransition;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEAComplement;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * Test Class for Pea Complement.
 *
 * @author Lena Funk
 */

@RunWith(JUnit4.class)
public class ComplementPEATest {

	ArrayList<PhaseEventAutomata> mTestAutomata;

	public ComplementPEATest() {
		mTestAutomata = new ArrayList<>();

		final PhaseEventAutomata responseDelayGlobally = createResponseDelayGloballyPea();
		final PhaseEventAutomata universalityGlobally = createUniversalityGloballyPea();
		final PhaseEventAutomata durationBoundUGlobally = createDurationBoundUGlobally();
		createDurationBoundUGloballyModified();
		final PhaseEventAutomata universalityDelayGlobally = createUniversalityDelayGloballyPea();

		mTestAutomata.add(responseDelayGlobally);
		mTestAutomata.add(universalityGlobally);
		mTestAutomata.add(durationBoundUGlobally);
		mTestAutomata.add(universalityDelayGlobally);
	}

	// constructs a PEA corresponding to pattern UniversalityGlobally
	public PhaseEventAutomata createUniversalityGloballyPea() {
		final String vR = "R";
		final Map<String, String> variables = new HashMap<>();
		variables.put(vR, "boolean");
		final CDD r = BooleanDecision.create(vR);
		final Phase[] phases = { new Phase("0", r, CDD.TRUE) };
		final String[] noreset = {};
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		return new PhaseEventAutomata("UniversalityGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition(CDD.TRUE, phases[0])), Collections.emptyList(), variables,
				Collections.emptyList());
	}

	// constructs a PEA corresponding to pattern ResponseDelay Globally
	public PhaseEventAutomata createResponseDelayGloballyPea() {
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

		return new PhaseEventAutomata("ResponseDelayGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition(CDD.TRUE, phases[0]), new InitialTransition(CDD.TRUE, phases[1])),
				clocks, variables, Collections.emptyList());
	}

	/**
	 * Constructs a PEA corresponding to pattern DurationBoundUGlobally: Globally, it is always the case that once "R"
	 * becomes satisfied, it holds for less than "5" time units
	 *
	 * @return the PEA
	 */
	public PhaseEventAutomata createDurationBoundUGlobally() {
		final Map<String, String> variables = new HashMap<>();
		final CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		final CDD notR = r.negate();
		final CDD clkInv = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
		final List<String> clocks = new ArrayList<>();
		clocks.add("c0");

		final Phase[] phases = { new Phase("0", notR, CDD.TRUE), new Phase("1", r, clkInv) };

		final String[] reset = { "c0" };
		final String[] noreset = {};

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);

		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], CDD.TRUE, noreset);

		return new PhaseEventAutomata("DurationBoundUGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition(CDD.TRUE, phases[0]), new InitialTransition(CDD.TRUE, phases[1])),
				clocks, variables, Collections.emptyList());
	}

	public PhaseEventAutomata createDurationBoundUGloballyModified() {
		final Map<String, String> variables = new HashMap<>();
		final CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		final CDD notR = r.negate();
		final CDD strictConstraint = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
		final CDD nonStrictConstraint = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		final CDD clkInv = strictConstraint.and(nonStrictConstraint);
		clkInv.getDecision().getVar();

		final Phase[] phases = { new Phase("0", notR, CDD.TRUE), new Phase("1", r, clkInv) };

		final String[] reset = { "c0" };
		final String[] noreset = {};

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);

		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], CDD.TRUE, noreset);

		final List<String> clocks = new ArrayList<>();
		clocks.add("c0");
		clocks.add("c1");

		return new PhaseEventAutomata("DurationBoundUGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition(CDD.TRUE, phases[0]), new InitialTransition(CDD.TRUE, phases[1])),
				clocks, variables, Collections.emptyList());
	}

	/**
	 * Constructs a PEA corresponding to pattern UniversalityDelayGlobally: Globally, it is always the case that "R"
	 * holds after at most "7" time units
	 *
	 * @return the PEA
	 */
	public PhaseEventAutomata createUniversalityDelayGloballyPea() {
		final Map<String, String> variables = new HashMap<>();
		final CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		final CDD clkInv = RangeDecision.create("c0", RangeDecision.OP_LTEQ, 7);
		final CDD clkGuardLoop = RangeDecision.create("c0", RangeDecision.OP_LT, 7);
		final CDD clkGuardProgress = RangeDecision.create("c0", RangeDecision.OP_GTEQ, 7);
		final List<String> clocks = new ArrayList<>();
		clocks.add("c0");
		final Phase[] phases = { new Phase("0", CDD.TRUE, clkInv), new Phase("1", r, CDD.TRUE) };
		final String[] noreset = {};

		// loop transitions
		phases[0].addTransition(phases[0], clkGuardLoop, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);

		// progress transition
		phases[0].addTransition(phases[1], clkGuardProgress, noreset);

		return new PhaseEventAutomata("UniversalityDelayGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition(CDD.TRUE, phases[0])), clocks, variables, Collections.emptyList());
	}

	public CDD constructMultiClockInvariant() {
		final CDD clkInv1 = RangeDecision.create("clk1", RangeDecision.OP_LTEQ, 5);
		final CDD clkInv2 = RangeDecision.create("clk2", RangeDecision.OP_LT, 6);
		final CDD clkInv3 = RangeDecision.create("clk3", RangeDecision.OP_GTEQ, 5);
		final CDD clkInv4 = RangeDecision.create("clk4", RangeDecision.OP_GT, 6);

		return clkInv1.and(clkInv2).and(clkInv3).and(clkInv4);
	}

	public Boolean comparePhases(final Phase phaseA, final Phase phaseB) {
		return ((phaseA.getStateInvariant() == phaseB.getStateInvariant()) && (phaseA.getClockInvariant() == phaseB.getClockInvariant()));
	}

	/**
	 * Test PEA: ResponseDelayGlobally
	 *
	 * Sink is not initial
	 */
	@Test
	public void testComplementResponseDelayGlobally() {
		final PhaseEventAutomata testPEA = mTestAutomata.get(0);
		final PEAComplement complementPEA = new PEAComplement(testPEA);
		final PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		final List<Phase> originalPhases = testPEA.getPhases();
		final List<Phase> phases = complementAutomaton.getPhases();
		assertEquals(originalPhases.size(), phases.size() - 1);
		// does the complement automaton contain a sink?
		final Phase sink =
				phases.stream().filter(p -> PEAComplement.SINK_NAME.equals(p.getName())).findAny().orElse(null);
		assertTrue(PEAComplement.SINK_NAME.equals(sink.getName()));
		// is it accepting?
		assertTrue(sink.getTerminal());
		// it should not be initial
		assertTrue(!sink.isInit());
		assertTrue(sink.getInitialTransition() == null);

	}

	/**
	 * Test PEA: UniversalityGlobally
	 *
	 * Case where sink is initial
	 */
	@Test
	public void testComplementUniversalityGlobally() {
		final PhaseEventAutomata testPEA = mTestAutomata.get(1);
		final PEAComplement complementPEA = new PEAComplement(testPEA);
		final PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		final List<Phase> phases = complementAutomaton.getPhases();
		final Phase sink =
				phases.stream().filter(p -> PEAComplement.SINK_NAME.equals(p.getName())).findAny().orElse(null);
		assertTrue(sink.getInitialTransition() != null);
		final InitialTransition sinkInitialTransition = sink.getInitialTransition();
		final CDD guard = sinkInitialTransition.getGuard();
		final CDD expected = BooleanDecision.create("R").negate();
		assertTrue(guard.equals(expected));
	}

	/**
	 * Test PEA: DurationBoundUGlobally
	 *
	 * Special case with countertrace phi = ... l >= T; true
	 */
	@Test
	public void testComplementDurationBoundUGlobally() {
		final PhaseEventAutomata testPEA = mTestAutomata.get(2);
		final PEAComplement complementPEA = new PEAComplement(testPEA);
		final PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		final List<Phase> phases = complementAutomaton.getPhases();
		assertTrue(phases.size() == testPEA.getPhases().size() + 1);
		final Phase sink = phases.stream().filter(p -> "sink".equals(p.getName())).findAny().orElse(null);
		assertTrue("sink".equals(sink.getName()));
		assertTrue(sink.getTerminal());
		final Phase phase1 = phases.stream().filter(p -> p.getClockInvariant() != CDD.TRUE).findAny().orElse(null);
		final CDD expectedClkInv =
				RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_LTEQ, 5);
		assert phase1 != null;
		assertEquals(expectedClkInv, phase1.getClockInvariant());
		final List<Transition> phase1OutgoingTransitions = phase1.getTransitions();
		final Map<Phase, CDD> expectedSinkGuard = new HashMap<>();
		expectedSinkGuard.put(phase1,
				RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GTEQ, 5));
		expectedSinkGuard.put(phases.get(0), CDD.FALSE);
		for (final Transition transition : phase1OutgoingTransitions) {
			if (transition.getDest() != sink) {
				final CDD expectedGuard =
						RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_LT, 5);
				assertEquals(expectedGuard, transition.getGuard());
			} else {
				assertEquals(expectedSinkGuard.get(transition.getSrc()), transition.getGuard());
			}
		}
		assertTrue(phase1.getModifiedConstraints().size() == 1);
	}

	/**
	 * Test PEA: UniversalityDelayGlobally
	 *
	 * Case that shows that sink guard must consider non-strict current clock invariant.
	 */
	@Test
	public void testComplementUniversalityDelayGlobally() {
		final PhaseEventAutomata testPEA = mTestAutomata.get(3);
		final PEAComplement complementPEA = new PEAComplement(testPEA);
		final PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		final List<Phase> phases = complementAutomaton.getPhases();
		// contains 1 additional location
		assertTrue(phases.size() == testPEA.getPhases().size() + 1);
		final Phase sink = phases.stream().filter(p -> "sink".equals(p.getName())).findAny().orElse(null);
		// contains sink location that is accepting
		assertTrue("sink".equals(sink.getName()));
		assertTrue(sink.getTerminal());
		// sink should not be initial
		assertTrue(!sink.isInit());
		assertTrue(sink.getInitialTransition() == null);

		// Check that Clock Invariants are not modified
		final Phase phase0 = phases.get(0);
		final CDD expectedClkInvPhase0 =
				RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_LTEQ, 7);
		assertEquals(expectedClkInvPhase0, phase0.getClockInvariant());
		final Phase phase1 = phases.get(1);
		final CDD expectedClkInvPhase1 = CDD.TRUE;
		assertEquals(expectedClkInvPhase1, phase1.getClockInvariant());

		final Set<String> ignoreId = new HashSet<>();

		final List<Transition> phase0OutgoingTransitions = phase0.getTransitions();
		final Map<Phase, CDD> expectedSinkGuard = new HashMap<>();
		expectedSinkGuard.put(phase0,
				RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GT, 7).or(BooleanDecision
						.create("R").prime(ignoreId).negate()
						.and(RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GTEQ, 7))));
		expectedSinkGuard.put(phases.get(1), CDD.FALSE);

		// Check guards of all outgoing transitions from phase 0
		for (final Transition transition : phase0OutgoingTransitions) {
			if (transition.getDest() == phase0) {
				final CDD expectedGuard =
						RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_LT, 7);
				assertEquals(expectedGuard, transition.getGuard());
			} else if (transition.getDest() == phase1) {
				final CDD expectedGuard =
						RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GTEQ, 7);
				assertEquals(expectedGuard, transition.getGuard());
			} else {
				assertEquals(expectedSinkGuard.get(transition.getSrc()), transition.getGuard());
			}
		}
	}

}