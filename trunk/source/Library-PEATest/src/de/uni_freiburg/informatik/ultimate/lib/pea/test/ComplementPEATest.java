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
import java.util.List;
import java.util.jar.Attributes.Name;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.ComplementPEA;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
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
	
	// constructs a PEA corresponding to pattern UniversalityGlobally
	public PhaseEventAutomata createUniversalityGloballyPea() {
		// variablen? initialkante? 
		CDD r = BooleanDecision.create("R");
		final Phase[] phases = new Phase[] { new Phase("0", r, CDD.TRUE)};
		final String[] noreset = new String[0];
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		return new PhaseEventAutomata("UniversalityGlobally", phases, new Phase[] { phases[0] });
	}
	
	// constructs a PEA corresponding to pattern ResponseDelay Globally
	public PhaseEventAutomata createResponseDelayGloballyPea() {
		
		// variablen? initialkante? 
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
	
	@Test
	public void checkPeaConstruction() {
		PhaseEventAutomata UniversalityGlobally = createUniversalityGloballyPea();
		PhaseEventAutomata ResponseDelayGlobally = createResponseDelayGloballyPea();
		Phase[] init = UniversalityGlobally.getInit();
		// wo initialkante.
	}
	

	
	@Test
	public void testComplementResponseDelayGlobally() {
		PhaseEventAutomata responseDelayGlobally = createResponseDelayGloballyPea();
		ComplementPEA complementPEA = new ComplementPEA(responseDelayGlobally);
		PhaseEventAutomata complementAutomaton = complementPEA.complement();
		Phase[] originalPhases = responseDelayGlobally.getPhases();
		Phase[] phases = complementAutomaton.getPhases();
		// does the complement automaton contain a sink? 
		Phase sink = phases[0];
		assertTrue(sink.getName() == "sink");
		// is it accepting?
		assertTrue(sink.getAccepting());
		// it should not be initial
		assertTrue(sink.isInit == false);
		assertTrue(!sink.getInitialTransition().isPresent());
		assertEquals(originalPhases.length, phases.length - 1);
	}
	
	@Test 
	public void testNoReset1() {
		CDD clkInv1 = RangeDecision.create("clk1",  RangeDecision.OP_LTEQ, 5);
		CDD clkInv2 = RangeDecision.create("clk2",  RangeDecision.OP_LTEQ, 5);
		CDD clkInv3 = RangeDecision.create("clk3",  RangeDecision.OP_LTEQ, 5);
		CDD clkInvOr = clkInv2.or(clkInv3);
		CDD clkInvCombi = clkInv1.and(clkInvOr);
		String clkInvString = clkInvCombi.toString();
		CDD[] cnf = clkInvCombi.toCNF();
		String cnfString = cnf.toString();
	}
	
}
