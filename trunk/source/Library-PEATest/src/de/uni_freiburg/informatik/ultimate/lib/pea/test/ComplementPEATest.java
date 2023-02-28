package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
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
	
	
	@Test
	public void testPeaConstruction_1() {
		PhaseEventAutomata UniversalityGlobally = createUniversalityGloballyPea();
		PhaseEventAutomata ResponseDelayGlobally = createResponseDelayGloballyPea();
		Phase[] init = UniversalityGlobally.getInit();
		// wo initialkante.
	}
	
}
