package de.uni_freiburg.informatik.ultimate.pea2boogie;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.Req2Pea;

/**
 * Test Class for Nonterminal Violable Phase generation.
 *
 *
 * @author Abigail Durst <dursta@informatik.uni-freiburg.de>
 */

@RunWith(JUnit4.class)
public class NvpTest {
	
	// List of example PEAs to test on
	ArrayList<PhaseEventAutomata> mTestAutomata;

	public NvpTest() {
		mTestAutomata = new ArrayList<PhaseEventAutomata>();
		
		// Example which contains both true last phases and pseudo last phases
		PhaseEventAutomata nameofPEA1 = createNameOfPEA1();
		mTestAutomata.add(nameofPEA1);
		
		// Example which contains both seeping phases
		PhaseEventAutomata nameofPEA2 = createNameOfPEA2();
		mTestAutomata.add(nameofPEA2);
		
		// Example which contains violable phases due to clocks
		PhaseEventAutomata nameofPEA3 = createNameOfPEA3();
		mTestAutomata.add(nameofPEA3);

	}
	
	public PhaseEventAutomata createNameOfPEA1() {
		PhaseEventAutomata pea1 = null;
		
		return pea1;
	}
	
	public PhaseEventAutomata createNameOfPEA2() {
		PhaseEventAutomata pea2 = null;
		
		return pea2;
	}
	
	public PhaseEventAutomata createNameOfPEA3() {
		PhaseEventAutomata pea3 = null;
		
		return pea3;
	}
	
	// generate the NVPs for each PEA in mTestAutomata and test them
}