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
		mTestAutomata = new ArrayList<PhaseEventAutomata>();

		PhaseEventAutomata ResponseDelayGlobally = createResponseDelayGloballyPea();
		PhaseEventAutomata UniversalityGlobally = createUniversalityGloballyPea();
		PhaseEventAutomata DurationBoundUGlobally = createDurationBoundUGlobally();
		PhaseEventAutomata durationBoundUGloballyModified = createDurationBoundUGloballyModified();
		PhaseEventAutomata UniversalityDelayGlobally = createUniversalityDelayGloballyPea();

		mTestAutomata.add(ResponseDelayGlobally);
		mTestAutomata.add(UniversalityGlobally);
		mTestAutomata.add(DurationBoundUGlobally);
		mTestAutomata.add(UniversalityDelayGlobally);
	}

	// constructs a PEA corresponding to pattern UniversalityGlobally
	public PhaseEventAutomata createUniversalityGloballyPea() {
		String vR = "R";
		Map<String, String> variables = new HashMap<String, String>();
		variables.put(vR, "boolean");
		CDD r = BooleanDecision.create(vR);
		final Phase[] phases = new Phase[] { new Phase("0", r, CDD.TRUE) };
		final String[] noreset = new String[0];
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		return new PhaseEventAutomata("UniversalityGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition[] { new InitialTransition(CDD.TRUE, phases[0]) }),
				Collections.emptyList(), variables, Collections.emptyList());
	}

	// constructs a PEA corresponding to pattern ResponseDelay Globally
	public PhaseEventAutomata createResponseDelayGloballyPea() {
		Map<String, String> variables = new HashMap<String, String>();
		CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		CDD s = BooleanDecision.create("S");
		variables.put("S", "boolean");
		CDD locInv0 = s.or(r.negate());
		CDD locInv1 = r.and(s.negate());
		CDD locInv2 = r.negate().and(s.negate());
		CDD clkInv = RangeDecision.create("clk", RangeDecision.OP_LTEQ, 5);
		CDD clkGuard = RangeDecision.create("clk", RangeDecision.OP_LT, 5);

		ArrayList<String> clocks = new ArrayList<String>();
		clocks.add("clk");

		final String[] reset = new String[] { "clk" };
		final String[] noreset = new String[0];

		final Phase[] phases = new Phase[] { new Phase("0", locInv0, CDD.TRUE), new Phase("1", locInv1, clkInv),
				new Phase("2", locInv2, clkInv) };

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

		return new PhaseEventAutomata(
				"ResponseDelayGlobally", Arrays.asList(phases), Arrays.asList(new InitialTransition[] {
						new InitialTransition(CDD.TRUE, phases[0]), new InitialTransition(CDD.TRUE, phases[1]) }),
				clocks, variables, Collections.emptyList());
	}

	/**
	 * Constructs a PEA corresponding to pattern DurationBoundUGlobally: Globally, it is always the case that once "R"
	 * becomes satisfied, it holds for less than "5" time units
	 * 
	 * @return the PEA
	 */
	public PhaseEventAutomata createDurationBoundUGlobally() {
		Map<String, String> variables = new HashMap<String, String>();
		CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		CDD notR = r.negate();
		CDD clkInv = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
		ArrayList<String> clocks = new ArrayList<String>();
		clocks.add("c0");

		final Phase[] phases = new Phase[] { new Phase("0", notR, CDD.TRUE), new Phase("1", r, clkInv) };

		final String[] reset = new String[] { "c0" };
		final String[] noreset = new String[0];

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);

		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], CDD.TRUE, noreset);

		return new PhaseEventAutomata(
				"DurationBoundUGlobally", Arrays.asList(phases), Arrays.asList(new InitialTransition[] {
						new InitialTransition(CDD.TRUE, phases[0]), new InitialTransition(CDD.TRUE, phases[1]) }),
				clocks, variables, Collections.emptyList());
	}

	public PhaseEventAutomata createDurationBoundUGloballyModified() {
		Map<String, String> variables = new HashMap<String, String>();
		CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		CDD notR = r.negate();
		CDD strictConstraint = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
		CDD nonStrictConstraint = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		CDD clkInv = strictConstraint.and(nonStrictConstraint);
		String varString = clkInv.getDecision().getVar();

		final Phase[] phases = new Phase[] { new Phase("0", notR, CDD.TRUE), new Phase("1", r, clkInv) };

		final String[] reset = new String[] { "c0" };
		final String[] noreset = new String[0];

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);

		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], CDD.TRUE, noreset);

		ArrayList<String> clocks = new ArrayList<String>();
		clocks.add("c0");
		clocks.add("c1");

		return new PhaseEventAutomata(
				"DurationBoundUGlobally", Arrays.asList(phases), Arrays.asList(new InitialTransition[] {
						new InitialTransition(CDD.TRUE, phases[0]), new InitialTransition(CDD.TRUE, phases[1]) }),
				clocks, variables, Collections.emptyList());
	}

	/**
	 * Constructs a PEA corresponding to pattern UniversalityDelayGlobally: Globally, it is always the case that "R" 
	 * holds after at most "7" time units
	 * 
	 * @return the PEA
	 */
	public PhaseEventAutomata createUniversalityDelayGloballyPea() {
		Map<String, String> variables = new HashMap<String, String>();
		CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		CDD clkInv = RangeDecision.create("c0", RangeDecision.OP_LTEQ, 7);
		CDD clkGuardLoop = RangeDecision.create("c0", RangeDecision.OP_LT, 7);
		CDD clkGuardProgress = RangeDecision.create("c0", RangeDecision.OP_GTEQ, 7);
		ArrayList<String> clocks = new ArrayList<String>();
		clocks.add("c0");
		final Phase[] phases = new Phase[] { new Phase("0", CDD.TRUE, clkInv), new Phase("1", r, CDD.TRUE) };
		final String[] noreset = new String[0];
		
		// loop transitions
		phases[0].addTransition(phases[0], clkGuardLoop, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);
		
		// progress transition
		phases[0].addTransition(phases[1], clkGuardProgress, noreset);
		
		return new PhaseEventAutomata("UniversalityDelayGlobally", Arrays.asList(phases),
				Arrays.asList(new InitialTransition[] { new InitialTransition(CDD.TRUE, phases[0]) }),
				clocks, variables, Collections.emptyList());
	}
	
	public CDD constructMultiClockInvariant() {
		CDD clkInv1 = RangeDecision.create("clk1", RangeDecision.OP_LTEQ, 5);
		CDD clkInv2 = RangeDecision.create("clk2", RangeDecision.OP_LT, 6);
		CDD clkInv3 = RangeDecision.create("clk3", RangeDecision.OP_GTEQ, 5);
		CDD clkInv4 = RangeDecision.create("clk4", RangeDecision.OP_GT, 6);

		CDD multiClock = clkInv1.and(clkInv2).and(clkInv3).and(clkInv4);
		return multiClock;
	}

	public Boolean comparePhases(Phase phaseA, Phase phaseB) {
		if (phaseA.getStateInvariant() != phaseB.getStateInvariant()
				|| phaseA.getClockInvariant() != phaseB.getClockInvariant()) {
			return false;
		}
		return true;
	}

	/**
	 * Test PEA: ResponseDelayGlobally
	 * 
	 * Sink is not initial
	 */
	@Test
	public void testComplementResponseDelayGlobally() {
		PhaseEventAutomata testPEA = mTestAutomata.get(0);
		PEAComplement complementPEA = new PEAComplement(testPEA);
		PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		List<Phase> originalPhases = testPEA.getPhases();
		List<Phase> phases = complementAutomaton.getPhases();
		assertEquals(originalPhases.size(), phases.size() - 1);
		// does the complement automaton contain a sink?
		Phase sink = phases.stream().filter(p -> p.getName().equals(PEAComplement.SINK_NAME)).findAny().orElse(null);
		assertTrue(sink.getName().equals(PEAComplement.SINK_NAME));
		// is it accepting?
		assertTrue(sink.getTerminal());
		// it should not be initial
		assertTrue(sink.isInit == false);
		assertTrue(sink.getInitialTransition() == null);

	}

	/**
	 * Test PEA: UniversalityGlobally
	 * 
	 * Case where sink is initial
	 */
	@Test
	public void testComplementUniversalityGlobally() {
		PhaseEventAutomata testPEA = mTestAutomata.get(1);
		PEAComplement complementPEA = new PEAComplement(testPEA);
		PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		List<Phase> phases = complementAutomaton.getPhases();
		Phase sink = phases.stream().filter(p -> p.getName().equals(PEAComplement.SINK_NAME)).findAny().orElse(null);
		assertTrue(sink.getInitialTransition() != null);
		InitialTransition sinkInitialTransition = sink.getInitialTransition();
		CDD guard = sinkInitialTransition.getGuard();
		CDD expected = BooleanDecision.create("R").negate();
		assertTrue(guard.equals(expected));
	}

	/**
	 * Test PEA: DurationBoundUGlobally
	 * 
	 * Special case with countertrace phi = ... l >= T; true
	 */
	@Test
	public void testComplementDurationBoundUGlobally() {
		PhaseEventAutomata testPEA = mTestAutomata.get(2);
		PEAComplement complementPEA = new PEAComplement(testPEA);
		PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		List<Phase> phases = complementAutomaton.getPhases();
		assertTrue(phases.size() == testPEA.getPhases().size() + 1);
		Phase sink = phases.stream().filter(p -> p.getName().equals("sink")).findAny().orElse(null);
		assertTrue(sink.getName().equals("sink"));
		assertTrue(sink.getTerminal());
		Phase phase1 = phases.stream().filter(p -> p.getClockInvariant() != CDD.TRUE).findAny().orElse(null);
		CDD expectedClkInv = RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_LTEQ, 5);
		assertEquals(expectedClkInv, phase1.getClockInvariant());
		List<Transition> phase1OutgoingTransitions = phase1.getTransitions();
		HashMap<Phase, CDD> expectedSinkGuard = new HashMap();
		expectedSinkGuard.put(phase1,
				RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GTEQ, 5));
		expectedSinkGuard.put(phases.get(0), CDD.FALSE);
		for (Transition transition : phase1OutgoingTransitions) {
			if (transition.getDest() != sink) {
				CDD expectedGuard =
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
		PhaseEventAutomata testPEA = mTestAutomata.get(3);
		PEAComplement complementPEA = new PEAComplement(testPEA);
		PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		List<Phase> phases = complementAutomaton.getPhases();
		// contains 1 additional location
		assertTrue(phases.size() == testPEA.getPhases().size() + 1);
		Phase sink = phases.stream().filter(p -> p.getName().equals("sink")).findAny().orElse(null);
		// contains sink location that is accepting
		assertTrue(sink.getName().equals("sink"));
		assertTrue(sink.getTerminal());
		// sink should not be initial
		assertTrue(sink.isInit == false);
		assertTrue(sink.getInitialTransition() == null);
		
		// Check that Clock Invariants are not modified
		Phase phase0 = phases.get(0);
		CDD expectedClkInvPhase0 = RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_LTEQ, 7);
		assertEquals(expectedClkInvPhase0, phase0.getClockInvariant());
		Phase phase1 = phases.get(1);
		CDD expectedClkInvPhase1 = CDD.TRUE;
		assertEquals(expectedClkInvPhase1, phase1.getClockInvariant());
		
		Set<String> ignoreId = new HashSet<>();
		
		List<Transition> phase0OutgoingTransitions = phase0.getTransitions();
		HashMap<Phase, CDD> expectedSinkGuard = new HashMap();
		expectedSinkGuard.put(phase0,
				RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GT, 7).or(BooleanDecision
						.create("R").prime(ignoreId).negate()
						.and(RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GTEQ, 7))));
		expectedSinkGuard.put(phases.get(1), CDD.FALSE);
		
		// Check guards of all outgoing transitions from phase 0
		for (Transition transition : phase0OutgoingTransitions) {
			if (transition.getDest() == phase0) {
				CDD expectedGuard =
						RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_LT, 7);
				assertEquals(expectedGuard, transition.getGuard());
			} else if (transition.getDest() == phase1) { 
				CDD expectedGuard =
						RangeDecision.create("c0" + PEAComplement.COMPLEMENT_POSTFIX, RangeDecision.OP_GTEQ, 7);
				assertEquals(expectedGuard, transition.getGuard());
			}
			else {
				assertEquals(expectedSinkGuard.get(transition.getSrc()), transition.getGuard());
			}
		}
	}

}