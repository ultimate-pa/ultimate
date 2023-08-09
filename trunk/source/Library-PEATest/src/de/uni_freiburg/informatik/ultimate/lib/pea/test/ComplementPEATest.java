package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.jar.Attributes.Name;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.ComplementPEA;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.InitialTransition;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseSet;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
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
		
		mTestAutomata.add(ResponseDelayGlobally);
		mTestAutomata.add(UniversalityGlobally);
		mTestAutomata.add(DurationBoundUGlobally);
	}
	
	// constructs a PEA corresponding to pattern UniversalityGlobally
	public PhaseEventAutomata createUniversalityGloballyPea() {
		CDD r = BooleanDecision.create("R");
		final Phase[] phases = new Phase[] { new Phase("0", r, CDD.TRUE)};
		final String[] noreset = new String[0];
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		return new PhaseEventAutomata("UniversalityGlobally", phases, new Phase[] { phases[0] });
	}
	
	// constructs a PEA corresponding to pattern ResponseDelay Globally
	public PhaseEventAutomata createResponseDelayGloballyPea() {
		CDD r = BooleanDecision.create("R");
		CDD s = BooleanDecision.create("S");
		CDD locInv0 = s.or(r.negate());
		CDD locInv1 = r.and(s.negate());
		CDD locInv2 = r.negate().and(s.negate());
		CDD clkInv = RangeDecision.create("clk",  RangeDecision.OP_LTEQ, 5);
		CDD clkGuard = RangeDecision.create("clk", RangeDecision.OP_LT, 5);
		
		final String[] reset = new String[] { "clk" };
		final String[] noreset = new String[0];
		
		
		final Phase[] phases = new Phase[] { new Phase("0", locInv0, CDD.TRUE), new Phase("1", locInv1, clkInv),
				new Phase("2", locInv2, clkInv)};
		
		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], clkGuard, noreset);
		phases[2].addTransition(phases[2], clkGuard, noreset);
		
		//transitions
		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], s, noreset);
		phases[1].addTransition(phases[2], clkGuard, noreset);
		phases[2].addTransition(phases[1], clkGuard, noreset);
		phases[2].addTransition(phases[0], s, noreset);

		return new PhaseEventAutomata("ResponseDelayGlobally", phases, new Phase[] { phases[0], phases[1] });
	}
	
	/**
	 * Constructs a PEA corresponding to pattern DurationBoundUGlobally:
	 * Globally, it is always the case that once "R" becomes satisfied, it holds for less than "5" time units
	 * 
	 * @return the PEA
	 */
	public PhaseEventAutomata createDurationBoundUGlobally() {
		CDD r = BooleanDecision.create("R");
		CDD notR = r.negate();
		CDD clkInv = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
		
		final Phase[] phases = new Phase[] { new Phase("0", notR, CDD.TRUE), new Phase("1", r, clkInv)};
		
		
		final String[] reset = new String[] { "c0" };
		final String[] noreset = new String[0];
		
		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);
		
		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], CDD.TRUE, noreset);
		
		
		return new PhaseEventAutomata("DurationBoundUGlobally", phases, new Phase[] { phases[0], phases[1] });
	}
	
	public PhaseEventAutomata createDurationBoundUGloballyModified() {
		CDD r = BooleanDecision.create("R");
		CDD notR = r.negate();
		CDD strictConstraint = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
		CDD nonStrictConstraint = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		CDD clkInv = strictConstraint.and(nonStrictConstraint);
		String varString = clkInv.getDecision().getVar();
		
		final Phase[] phases = new Phase[] { new Phase("0", notR, CDD.TRUE), new Phase("1", r, clkInv)};
		
		
		final String[] reset = new String[] { "c0" };
		final String[] noreset = new String[0];
		
		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);
		
		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], CDD.TRUE, noreset);
		
		
		return new PhaseEventAutomata("DurationBoundUGlobally", phases, new Phase[] { phases[0], phases[1] });
	}
	
	public CDD constructMultiClockInvariant() {
		CDD clkInv1 = RangeDecision.create("clk1",  RangeDecision.OP_LTEQ, 5);
		CDD clkInv2 = RangeDecision.create("clk2",  RangeDecision.OP_LT, 6);
		CDD clkInv3 = RangeDecision.create("clk3",  RangeDecision.OP_GTEQ, 5);
		CDD clkInv4 = RangeDecision.create("clk4",  RangeDecision.OP_GT, 6);
		
		CDD multiClock = clkInv1.and(clkInv2).and(clkInv3).and(clkInv4);
		return multiClock;
	}
	
	public Boolean comparePhases(Phase phaseA, Phase phaseB) {
		if (phaseA.getStateInvariant() != phaseB.getStateInvariant() || phaseA.getClockInvariant() != phaseB.getClockInvariant()) {
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
		ComplementPEA complementPEA = new ComplementPEA(testPEA);
		PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		Phase[] originalPhases = testPEA.getPhases();
		Phase[] phases = complementAutomaton.getPhases();
		assertEquals(originalPhases.length, phases.length - 1);
		// does the complement automaton contain a sink? 
		Phase sink = phases[0];
		assertTrue(sink.getName() == "sink");
		// is it accepting?
		assertTrue(sink.getTerminal());
		// it should not be initial
		assertTrue(sink.isInit == false);
		assertTrue(!sink.getInitialTransition().isPresent());
		
	}
	
	/**
	 * Test PEA: UniversalityGlobally
	 * 
	 * Case where sink is initial
	 */
	@Test
	public void testComplementUniversalityGlobally() {
		PhaseEventAutomata testPEA = mTestAutomata.get(1);
		ComplementPEA complementPEA = new ComplementPEA(testPEA);
		PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		Phase[] phases = complementAutomaton.getPhases();
		Phase sink = phases[0];
		assertTrue(sink.getInitialTransition().isPresent());
		InitialTransition sinkInitialTransition = sink.getInitialTransition().get();
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
		ComplementPEA complementPEA = new ComplementPEA(testPEA);
		PhaseEventAutomata complementAutomaton = complementPEA.getComplementPEA();
		Phase[] phases = complementAutomaton.getPhases();
		assertTrue(phases.length == testPEA.getPhases().length + 1);
		Phase sink = phases[0];
		assertTrue(sink.getTerminal());
		Phase originalPhase1 = phases[2];
		CDD expectedClkInv = RangeDecision.create("c0", RangeDecision.OP_LTEQ, 5);
		assertEquals(expectedClkInv, originalPhase1.getClockInvariant());
		List<Transition> phase1OutgoingTransitions = originalPhase1.getTransitions();
		for (Transition transition : phase1OutgoingTransitions) {
			if (transition.getDest() == phases[1]) {
				CDD expectedGuard = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
				assertEquals(expectedGuard, transition.getGuard());
			}
		}
	}
	
}
