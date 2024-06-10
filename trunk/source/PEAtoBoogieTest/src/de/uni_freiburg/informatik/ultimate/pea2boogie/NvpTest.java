package de.uni_freiburg.informatik.ultimate.pea2boogie;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.PeaViolablePhases;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateServiceProviderMock;

/**
 * Test Class for Nonterminal Violable Phase generation.
 *
 *
 * @author Abigail Durst <dursta@informatik.uni-freiburg.de>
 */

@RunWith(JUnit4.class)
public class NvpTest {
	
	// List of example PEAs to test on
	List<List<List<String>>> mNvpResults;
	ILogger mLogger;
	LogLevel info;
	IUltimateServiceProvider mServices;
	PeaResultUtil mPeaResultUtil;
	
	public NvpTest() {
		
		mLogger = ILogger.getDummyLogger();
		mLogger.setLevel(LogLevel.DEBUG);
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mPeaResultUtil = new PeaResultUtil(mLogger, mServices);
		mNvpResults = new ArrayList<List<List<String>>>();
		
		/*
		 * Example which contains violable phases due to clocks
		 * DurationBoundU Globally: Globally, it is always the case that once "R" becomes satisfied, it holds
		 * 
		 * Here, the NVP is [01X]
		 */
		PhaseEventAutomata DurationBoundUGlobally = createDurationBoundUGlobally();
		IReqSymbolTable symbolTableDurationBoundUGlobally = createSymbolTableDurationBoundUGlobally();
		final List<Declaration> declsDurationBoundUGlobally = new ArrayList<>();
		declsDurationBoundUGlobally.addAll(symbolTableDurationBoundUGlobally.getDeclarations());
		BoogieDeclarations boogieDeclarationsDurationBoundUGlobally = 
				new BoogieDeclarations(declsDurationBoundUGlobally, mLogger);
		
		// get NVPs
		PeaViolablePhases DurationBoundUGloballyViolablePhases = 
				new PeaViolablePhases(mLogger, mServices, mPeaResultUtil, 
						boogieDeclarationsDurationBoundUGlobally, symbolTableDurationBoundUGlobally, 
						DurationBoundUGlobally);
		List<List<Phase>> nvpResultDurationBoundUGlobally = DurationBoundUGloballyViolablePhases.nonterminalPeaViolablePhases();
		List<List<String>> nvpResultAsStringsDurationBoundUGlobally = new ArrayList<List<String>>();
		// get results as strings
		for (List<Phase> nvp : nvpResultDurationBoundUGlobally) {
			List<String> nvpAsStringsDurationBoundUGlobally = new ArrayList<String>();
			for (Phase p : nvp) {
				nvpAsStringsDurationBoundUGlobally.add(p.toString());
			}
			nvpResultAsStringsDurationBoundUGlobally.add(nvpAsStringsDurationBoundUGlobally);
		}
		mNvpResults.add(nvpResultAsStringsDurationBoundUGlobally);
		
		/*
		 * Example which contains both a true last phase and a seeping last phase
		 * PrecedenceChain12Globally: Globally, it is always the case that if "R" holds 
		 * 		and is succeeded by "S", then "T" previously held
		 * 
		 * Here, the NVPs are [12], [02, 012], and [0]
		
		
		PhaseEventAutomata PrecedenceChain12Globally = createPrecedenceChain12Globally();
		IReqSymbolTable symbolTablePrecedenceChain12Globally = createSymbolTableDurationBoundUGlobally();
		final List<Declaration> declsPrecedenceChain12Globally = new ArrayList<>();
		declsPrecedenceChain12Globally.addAll(symbolTablePrecedenceChain12Globally.getDeclarations());
		BoogieDeclarations boogieDeclarationsPrecedenceChain12Globally = 
				new BoogieDeclarations(declsPrecedenceChain12Globally, mLogger);
		
		// get NVPs
		PeaViolablePhases PrecedenceChain12GloballyViolablePhases = 
				new PeaViolablePhases(mLogger, mServices, mPeaResultUtil, 
						boogieDeclarationsDurationBoundUGlobally, symbolTableDurationBoundUGlobally, 
						DurationBoundUGlobally);
		List<List<Phase>> nvpResultPrecedenceChain12Globally = DurationBoundUGloballyViolablePhases.nonterminalPeaViolablePhases();
		List<List<String>> nvpResultAsStringsPrecedenceChain12Globally = new ArrayList<List<String>>();
		// get results as strings
		for (List<Phase> nvp : nvpResultPrecedenceChain12Globally) {
			List<String> nvpAsStringsPrecedenceChain12Globally = new ArrayList<String>();
			for (Phase p : nvp) {
				nvpAsStringsPrecedenceChain12Globally.add(p.toString());
			}
			nvpResultAsStringsPrecedenceChain12Globally.add(nvpAsStringsPrecedenceChain12Globally);
		}
		mNvpResults.add(nvpResultAsStringsPrecedenceChain12Globally);
		*/

		/*
		 * Example which contains non-typical pseudo last phases (non singular seeping phase)
		 * Precedence After: After "P", it is always the case that if "R" holds, then "S" previously held
		 * 
		 * Here, the NVPs are [0, 01, 012] and [01, 02, 012]
		 
		PhaseEventAutomata PrecedenceAfter = createPrecedenceAfter();
		IReqSymbolTable symbolTablePrecedenceAfter = createSymbolTableDurationBoundUGlobally();
		final List<Declaration> declsPrecedenceAfter = new ArrayList<>();
		declsPrecedenceAfter.addAll(symbolTablePrecedenceAfter.getDeclarations());
		BoogieDeclarations boogieDeclarationsPrecedenceAfter = 
				new BoogieDeclarations(declsPrecedenceAfter, mLogger);
		
		// get NVPs
		PeaViolablePhases PrecedenceAfterViolablePhases = 
				new PeaViolablePhases(mLogger, mServices, mPeaResultUtil, 
						boogieDeclarationsPrecedenceAfter, symbolTablePrecedenceAfter, 
						PrecedenceAfter);
		List<List<Phase>> nvpResultPrecedenceAfter = PrecedenceAfterViolablePhases.nonterminalPeaViolablePhases();
		List<List<String>> nvpResultAsStringsPrecedenceAfter = new ArrayList<List<String>>();
		// get results as strings
		for (List<Phase> nvp : nvpResultPrecedenceAfter) {
			List<String> nvpAsStringsPrecedenceAfter = new ArrayList<String>();
			for (Phase p : nvp) {
				nvpAsStringsPrecedenceAfter.add(p.toString());
			}
			nvpResultAsStringsPrecedenceAfter.add(nvpAsStringsPrecedenceAfter);
		}
		mNvpResults.add(nvpResultAsStringsPrecedenceAfter);
	*/
	}
	
	// DurationBoundUGlobally PEA generation taken from Lena Funk's PEA complement test file
	public PhaseEventAutomata createDurationBoundUGlobally() {
		Map<String, String> variables = new HashMap<String, String>();
		CDD r = BooleanDecision.create("R");
		variables.put("R", "boolean");
		CDD stateInv0 = r.negate();
		CDD clkInv = RangeDecision.create("c0", RangeDecision.OP_LT, 5);
		ArrayList<String> clocks = new ArrayList<String>();
		clocks.add("c0");

		final Phase[] phases = new Phase[] { new Phase("0", stateInv0, CDD.TRUE), new Phase("01X", r, clkInv) };
		final Phase[] initPhases = {phases[0], phases[1]};

		final String[] reset = new String[] { "c0" };
		final String[] noreset = new String[0];

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noreset);
		phases[1].addTransition(phases[1], CDD.TRUE, noreset);

		phases[0].addTransition(phases[1], CDD.TRUE, reset);
		phases[1].addTransition(phases[0], CDD.TRUE, noreset);

		return new PhaseEventAutomata("DurationBoundUGlobally", phases,
				initPhases, clocks, variables, Collections.emptyList());
	}
	
	public IReqSymbolTable createSymbolTableDurationBoundUGlobally() {
		ReqSymboltableBuilder tableBuilderDurationBoundUGlobally = 
				new ReqSymboltableBuilder(mLogger); 
		PhaseEventAutomata DurationBoundUGlobally = createDurationBoundUGlobally();
		tableBuilderDurationBoundUGlobally.addPea(null, DurationBoundUGlobally);
		IReqSymbolTable symbolTableDurationBoundUGlobally = 
				tableBuilderDurationBoundUGlobally.constructSymbolTable();
		return symbolTableDurationBoundUGlobally;
	}
	/*
	public PhaseEventAutomata createPrecedenceAfter() {
		// Define variables
		Map<String, String> variables = new HashMap<String, String>();
		CDD r = BooleanDecision.create("R");
		CDD p = BooleanDecision.create("P");
		CDD s = BooleanDecision.create("S");
		variables.put("R", "boolean");
		variables.put("P", "boolean");
		variables.put("S", "boolean");
		CDD notR = r.negate();
		CDD notS = s.negate();
		CDD notP = p.negate();
		ArrayList<String> clocks = new ArrayList<String>();
		
		// State invariants
		CDD stateInv0 = p.negate();
		CDD stateInv01 = p.and(s);
		CDD stateInv02 = notP.and(notR.and(notS));
		CDD stateInv012 = p.and(notR.and(notS));
		
		// Clock invariants
		CDD clkInv = CDD.TRUE;
		
		// Transition labels
		CDD from0to01 = CDD.TRUE;
		CDD from0to012 = CDD.TRUE;
		CDD from01to0 = s;
		CDD from01to02 = CDD.TRUE;
		CDD from01to012 = CDD.TRUE;
		CDD from02to0 = notR.and(s);
		CDD from02to01 = notR;
		CDD from02to012 = CDD.TRUE;
		CDD from012to0 = notR.and(s);
		CDD from012to01 = notR;
		CDD from012to02 = CDD.TRUE;

		final Phase[] phases = new Phase[] { new Phase("0", stateInv0, CDD.TRUE), new Phase("01", stateInv01, clkInv) ,
				new Phase("02", stateInv02, CDD.TRUE), new Phase("012", stateInv012, clkInv) };
		final Phase[] initPhases = {phases[0], phases[1], phases[3]};

		final String[] noReset = new String[0];

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noReset);
		phases[1].addTransition(phases[1], CDD.TRUE, noReset);
		phases[2].addTransition(phases[2], CDD.TRUE, noReset);
		phases[3].addTransition(phases[3], CDD.TRUE, noReset);

		// outgoing Phase 0
		phases[0].addTransition(phases[1], from0to01, noReset);
		phases[0].addTransition(phases[3], from0to012, noReset);
		
		// outgoing Phase 01
		phases[1].addTransition(phases[0], from01to0, noReset);
		phases[1].addTransition(phases[2], from01to02, noReset);
		phases[1].addTransition(phases[3], from01to012, noReset);
		
		// outgoing Phase 02
		phases[2].addTransition(phases[0], from02to0, noReset);
		phases[2].addTransition(phases[1], from02to01, noReset);
		phases[2].addTransition(phases[3], from02to012, noReset);
		
		// outgoing Phase 012
		phases[3].addTransition(phases[0], from012to0, noReset);
		phases[3].addTransition(phases[1], from012to01, noReset);
		phases[3].addTransition(phases[2], from012to02, noReset);

		return new PhaseEventAutomata("PrecedenceAfter", phases,
				initPhases, clocks, variables, Collections.emptyList());
	}
	
	
	
	public PhaseEventAutomata createPrecedenceChain12Globally() {
		// Define variables
		Map<String, String> variables = new HashMap<String, String>();
		CDD r = BooleanDecision.create("R");
		CDD t = BooleanDecision.create("T");
		CDD s = BooleanDecision.create("S");
		variables.put("R", "boolean");
		variables.put("T", "boolean");
		variables.put("S", "boolean");
		CDD notR = r.negate();
		CDD notS = s.negate();
		CDD notT = t.negate();
		ArrayList<String> clocks = new ArrayList<String>();
		
		// State invariants
		CDD stateInvInit = t;
		CDD stateInv = CDD.TRUE;
		CDD stateInv0 = notR.and(notT);
		CDD stateInv12 = r.and(notS);
		CDD stateInv012 = r.and(notS.and(notT));
		CDD stateInv02 = notR.and(notS.and(notT));
		CDD stateInv2 = notS;
		
		// Clock invariants
		CDD clkInv = CDD.TRUE;
		
		// Transition labels
		CDD fromInittoTrue = CDD.TRUE;
		CDD from0toTrue = notR.and(t);
		CDD from0to12 = t;
		CDD from0to012 = CDD.TRUE;
		CDD from012to2 = notR.and(t);
		CDD from012to02 = CDD.TRUE;
		CDD from012to12 = t;
		CDD from02to012 = CDD.TRUE;
		CDD from02to12 = t;
		CDD from02to2 = notR.and(t);
		CDD from12to2 = notR;

		final Phase[] phases = new Phase[] { new Phase("init", stateInvInit, clkInv), new Phase("true", stateInv, CDD.TRUE), 
				new Phase("0", stateInv0, clkInv), new Phase("012", stateInv012, clkInv), new Phase("02", stateInv02, clkInv), 
				new Phase("12", stateInv12, clkInv), new Phase("2", stateInv2, CDD.TRUE)};
		final Phase[] initPhases = {phases[0], phases[2], phases[3]};

		final String[] noReset = new String[0];

		// loop transitions
		phases[0].addTransition(phases[0], CDD.TRUE, noReset);
		phases[1].addTransition(phases[1], CDD.TRUE, noReset);
		phases[2].addTransition(phases[2], CDD.TRUE, noReset);
		phases[3].addTransition(phases[3], CDD.TRUE, noReset);
		phases[4].addTransition(phases[3], CDD.TRUE, noReset);
		phases[5].addTransition(phases[3], CDD.TRUE, noReset);
		phases[6].addTransition(phases[3], CDD.TRUE, noReset);


		// outgoing Phase init
		phases[0].addTransition(phases[1], fromInittoTrue, noReset);
		
		// outgoing Phase 0
		phases[2].addTransition(phases[1], from0toTrue, noReset);
		phases[2].addTransition(phases[3], from0to012, noReset);
		phases[2].addTransition(phases[5], from0to12, noReset);
		
		// outgoing Phase 012
		phases[3].addTransition(phases[4], from012to02, noReset);
		phases[3].addTransition(phases[5], from012to12, noReset);
		phases[3].addTransition(phases[6], from012to2, noReset);
		
		// outgoing Phase 02
		phases[4].addTransition(phases[3], from02to012, noReset);
		phases[4].addTransition(phases[5], from02to12, noReset);
		phases[4].addTransition(phases[6], from02to2, noReset);
		
		// outgoing Phase 12
		phases[5].addTransition(phases[6], from12to2, noReset);

		return new PhaseEventAutomata("PrecedenceChain12Globally", phases,
				initPhases, clocks, variables, Collections.emptyList());
	}
	*/
	
	/**
	 * Test NVPs of DurationBoundUGlobally
	 */
	@Test
	public void testNVPsOfDurationBoundUGlobally() {
		List<List<String>> DurationBoundUGloballyNvps = new ArrayList<>(Arrays.asList(Arrays.asList("01X")));
		assertEquals(mNvpResults.get(0), DurationBoundUGloballyNvps);
	}
	
	/**
	 * Test NVPs of PrecedenceChain12Globally
	 
	@Test
	public void testNVPsOfPrecedenceChain12Globally() {
		List<List<String>> PrecedenceChain12GloballyNvps = new ArrayList<>(
				Arrays.asList(Arrays.asList("02"), Arrays.asList("02", "012"), Arrays.asList("0")));
		assertEquals(mNvpResults.get(1), PrecedenceChain12GloballyNvps);
	}
	*/
	
	/**
	 * Test NVPs of PrecedenceAfter
	 
	@Test
	public void testNVPsOfPrecedenceAfter() {
		List<List<String>> PrecedenceAfterNvps = new ArrayList<>(Arrays.asList(Arrays.asList("0", "01", "012"), Arrays.asList("01", "02", "012")));
		assertEquals(mNvpResults.get(2), PrecedenceAfterNvps);
	}
	*/
}