package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DOTWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace;

public class TestCase {
	Trace2PeaCompiler compiler = new Trace2PeaCompiler(ILogger.getLogger(""));
	CDD entry = EventDecision.create("S1");
	CDD exit = EventDecision.create("S2");
	CDD missing = CDD.TRUE;
	DOTWriter j2DOTWriter = new DOTWriter("C:/vacuous/AmiTest.dot");

	public void runTest1() {
		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(A, CounterTrace.BOUND_GREATEREQUAL, 4),
		        new CounterTrace.DCPhase(B, CounterTrace.BOUND_LESS, 6) });
		final MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		ctA = compiler.compile("T1", mct);
		ctA.dump();

		final J2UPPAALWriter j2uppaalWriter = new J2UPPAALWriter();
		j2uppaalWriter.writePEA2UppaalFile("AmiTestT1.xml", ctA);
	}

	public void runTest2() {
		final CDD A = BooleanDecision.create("A");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(A, CounterTrace.BOUND_GREATEREQUAL, 4),
		        new CounterTrace.DCPhase(CounterTrace.BOUND_LESS, 6) });
		compiler.compile("T2", ct).dump();
	}

	public void runTest3() {
		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		final CounterTrace ct = new CounterTrace(
		        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(A, CounterTrace.BOUND_LESS, 1),
		                new CounterTrace.DCPhase(B, CounterTrace.BOUND_LESSEQUAL, 2) });
		MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		compiler.compile("T3", mct).dump();
		mct = new MCTrace(ct, null, exit, missing, true);
		compiler.compile("T4", mct).dump();
	}

	// Test Automat aus Jochens Diss S. 137ff
	public void runTest4() {
		final CDD A = BooleanDecision.create("A");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(A, CounterTrace.BOUND_GREATEREQUAL, 2), new CounterTrace.DCPhase() });
		compiler.compile("T5", ct).dump();
	}

	// Test Automat aus Jochens Diss S. 113ff
	// Formel true;B && l>=2; notB
	public void runTest5() {
		PhaseEventAutomata ctA;
		final CDD B = BooleanDecision.create("B");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(B, CounterTrace.BOUND_GREATEREQUAL, 2), new CounterTrace.DCPhase(B.negate()),
		        new CounterTrace.DCPhase() });
		ctA = compiler.compile("T5", ct);
		j2DOTWriter.write("C:/vacuous/test5.dot", ctA);
	}

	public void runTestVacuous() {
		PhaseEventAutomata ctA, ctA2;

		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(B.and(A.negate()), CounterTrace.BOUND_GREATER, 5),
		        new CounterTrace.DCPhase(A.negate(), CounterTrace.BOUND_GREATER, 10), new CounterTrace.DCPhase() });
		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(B, CounterTrace.BOUND_GREATER, 3), new CounterTrace.DCPhase() });
		ctA = compiler.compile("t", ct);
		j2DOTWriter.write("C:/vacuous/testVacuous_1.dot", ctA);
		ctA2 = compiler.compile("t2", ct2);
		j2DOTWriter.write("C:/vacuous/testVacuous_2.dot", ctA2);
		ctA2 = ctA2.parallel(ctA);
		j2DOTWriter.write("C:/vacuous/testVacuous_12.dot", ctA2);
		final J2UPPAALConverter uppaalConverter = new J2UPPAALConverter();
		uppaalConverter.writePEA2UppaalFile("C:/vacuous/testVacuous_12.xml", ctA2);
	}

	public void runTestVacuous2() {
		PhaseEventAutomata ctA, ctA2;

		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(B, CounterTrace.BOUND_GREATER, 5), new CounterTrace.DCPhase() });
		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(B, CounterTrace.BOUND_GREATEREQUAL, 5), new CounterTrace.DCPhase(A),
		        new CounterTrace.DCPhase() });
		ctA = compiler.compile("t", ct);
		j2DOTWriter.write("C:/vacuous/testVacuous_3.dot", ctA);
		ctA2 = compiler.compile("t2", ct2);
		j2DOTWriter.write("C:/vacuous/testVacuous_4.dot", ctA2);
		ctA2 = ctA2.parallel(ctA);
		j2DOTWriter.write("C:/vacuous/testVacuous_34.dot", ctA2);
		final J2UPPAALConverter uppaalConverter = new J2UPPAALConverter();
		uppaalConverter.writePEA2UppaalFile("C:/vacuous/testVacuous_34.xml", ctA2);
	}

	public void runTestSeeping() {
		final CDD B = BooleanDecision.create("B");
		final CDD A = BooleanDecision.create("A");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(B), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(A),
		        new CounterTrace.DCPhase(), new CounterTrace.DCPhase(B), new CounterTrace.DCPhase() });
		final PhaseEventAutomata ctA = compiler.compile("T5", ct);
		final DOTWriter j2uppaalWriter = new DOTWriter("C:/vacuous/AmiTest.dot");
		j2uppaalWriter.write("C:/vacuous/AmiTest.dot", ctA);
	}

	// Test Automat aus Jochens Diss S. 113ff
	// Formel true;B && l>=2; notB
	public void runTest5b() {
		final CDD B = BooleanDecision.create("B");
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE),
		        new CounterTrace.DCPhase(B, CounterTrace.BOUND_GREATEREQUAL, 2), new CounterTrace.DCPhase(B.negate()),
		        new CounterTrace.DCPhase() });
		ctA = compiler.compile("T5", ct);
		j2DOTWriter.write("C:/vacuous/test5b_notSimplified.dot", ctA);
		ctA.simplifyGuards();
		j2DOTWriter.write("C:/vacuous/test5b_simplified.dot", ctA);
	}

	// Test Automat aus Jochens Diss S. 139ff
	// Formel true;event(passed); l<=3; event(passed)
	public void runTest5c() {
		final CDD passed = EventDecision.create("passed");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(passed, CDD.TRUE, CounterTrace.BOUND_LESSEQUAL, 3),
		        new CounterTrace.DCPhase(passed, CDD.TRUE),
				// new CounterTrace.DCPhase()
		});
		compiler.compile("T5", ct).dump();

		// Formel current!= goal; current=goal && l>=2 && forbiddenEvent(Stop)
		final CDD current_goal = BooleanDecision.create("(current=goal)");
		final CDD current_NotGoal = current_goal.negate();
		// CDD stop = EventDecision.create('/', "stop");
		// Unklar: wie bekomme ich denn die EventDecision ins Set?
		// Wenn ich CounterTrace mit einem Set ungleich einem StringSet aufrufe gibts ne exception

		final Set forbid = Collections.singleton("stop");

		final CounterTrace ct2 = new CounterTrace(
		        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(current_NotGoal),
		                new CounterTrace.DCPhase(current_goal, CounterTrace.BOUND_GREATEREQUAL, 2, forbid),
		                new CounterTrace.DCPhase() });
		compiler.compile("T5b", ct2).dump();
	}

	// Test vacuously true anforderungen
	// Formel not(true;P, Q, neg(R) && l>=1; true)
	public void runTest6() {
		final CDD P = BooleanDecision.create("P");
		final CDD Q = BooleanDecision.create("Q");
		final CDD R = BooleanDecision.create("R");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        // new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE, CounterTrace.BOUND_NONE, 0,
		        // java.util.Collections.EMPTY_SET, false),
		        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(Q),
		        new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_GREATEREQUAL, 1), new CounterTrace.DCPhase() });
		compiler.compile("T6", ct).dump();
	}

	// Test vacuously true anforderungen
	// Formel not(true;P, Q, neg(R) && l>=1; true)
	public void runTest7() {
		final CDD P = BooleanDecision.create("P");
		final CDD Q = BooleanDecision.create("Q");
		final CDD R = BooleanDecision.create("R");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        // new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE, CounterTrace.BOUND_NONE, 0,
		        // java.util.Collections.EMPTY_SET, false),
		        new CounterTrace.DCPhase(P.and(Q.negate())), new CounterTrace.DCPhase(Q.and(R.negate())),
		        new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_GREATEREQUAL, 1), new CounterTrace.DCPhase() });
		compiler.compile("T7", ct).dump();
	}

	// Test vacuously true Anforderungen
	// Formel not(true;P & neg(Q); true) f�r P-->Q
	public void runTest7b() {
		final CDD P = BooleanDecision.create("P");
		final CDD Q = BooleanDecision.create("Q");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        // new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE, CounterTrace.BOUND_NONE, 0,
		        // java.util.Collections.EMPTY_SET, false),
		        new CounterTrace.DCPhase(P.and(Q.negate())), new CounterTrace.DCPhase() });
		compiler.compile("T7b", ct).dump();
	}

	// Test vacuously true Anforderungen
	// Formel not(true;P; true; neg(Q); true) f�r G(P-->G Q)
	public PhaseEventAutomata runTest7c(final CDD P, final CDD Q) {
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        // new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE, CounterTrace.BOUND_NONE, 0,
		        // java.util.Collections.EMPTY_SET, false),
		        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q.negate()),
		        new CounterTrace.DCPhase() });
		ctA = compiler.compile("T7c", ct);
		ctA.dump();
		return ctA;
	}

	// Test vacuously true Anforderungen
	// Formel not(true;P; l<1; Q; neg(R) & l>1; true) f�r G(P-->X(q --> Xr))
	// vacuous true f�r G(neg(P)) sowie f�r G(P-->Xneg(Q))
	public void runTest7d() {
		final CDD P = BooleanDecision.create("P");
		final CDD Q = BooleanDecision.create("Q");
		final CDD R = BooleanDecision.create("R");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        // new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE, CounterTrace.BOUND_NONE, 0,
		        // java.util.Collections.EMPTY_SET, false),
		        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(CDD.TRUE, CounterTrace.BOUND_LESS, 1),
		        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_GREATER, 1),
		        new CounterTrace.DCPhase() });
		compiler.compile("T7d", ct).dump();
	}

	// was passiert bei \neg(CDD.true)
	public void runTestTrue() {
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
		        // new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(CDD.FALSE), new CounterTrace.DCPhase() });
		compiler.compile("T7d", ct).dump();
	}

	// Test vacuously true Anforderungen
	// Formel not(true;P & l<1; Q & l>1; true) f�r G(P-->X(neg(q)))
	// vacuous true f�r G(neg(P))
	public void runTest7e() {
		final CDD P = BooleanDecision.create("P");
		final CDD Q = BooleanDecision.create("Q");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        // new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE, CounterTrace.BOUND_NONE, 0,
		        // java.util.Collections.EMPTY_SET, false),
		        new CounterTrace.DCPhase(P, Q, CounterTrace.BOUND_GREATER, 1), new CounterTrace.DCPhase() });
		compiler.compile("T7e", ct).dump();
	}

	// Test vacuously true Anforderungen
	// Formel not(true;event P; event Q; not event R; true) f�r G(P-->X(q-->Xr)))
	// vacuous true f�r G(neg(P))
	public void runTest7f() {
		final CDD P = BooleanDecision.create("P");
		final CDD Q = BooleanDecision.create("Q");
		final CDD R = BooleanDecision.create("R");
		// Set forbid = Collections.singleton("R");
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(P, CDD.TRUE, CounterTrace.BOUND_LESS, 1),
		        new CounterTrace.DCPhase(Q, R.negate(), CounterTrace.BOUND_GREATER, 1), new CounterTrace.DCPhase() });
		compiler.compile("T7e", ct).dump();
	}

	// Test vacuously true Anforderungen
	// Formel not(true;event A & neg(B); B & neg(C); true) f�r G(A-->(neg(B) U C))
	// vacuous true f�r G(neg(P))
	public void runTest7g() {
		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		final CDD C = BooleanDecision.create("C");
		PhaseEventAutomata ctParallel, ct1A, ct2A;

		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(A.and(C.negate()), B.negate().and(C.negate())),
		        new CounterTrace.DCPhase(B.and(C.negate())),
		        // new CounterTrace.DCPhase(B, C.negate()),
		        new CounterTrace.DCPhase() });
		ct1A = compiler.compile("T7g", ct);
		ct1A.dump();

		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(A, B.and(C.negate())), new CounterTrace.DCPhase() });
		ct2A = compiler.compile("T7g2", ct2);
		ct2A.dump();

		ctParallel = ct1A.parallel(ct2A);
		ctParallel.dump();

	}

	// Test vacuously true Anforderungen
	// f�r A-->G(B U C)
	// Formel1 not(true;A && neg(B) && neg(C); true)
	// vacuous true f�r G(neg A), G(C), G(A&&B&&negC)
	public void runTest7h() {
		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		final CDD C = BooleanDecision.create("C");
		PhaseEventAutomata ctParallel, ct1A, ct2A;

		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(A.and(B.negate().and(C.negate()))), new CounterTrace.DCPhase() });

		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(A.and(B.and(C.negate()))), new CounterTrace.DCPhase(B.and(C.negate())),
		        new CounterTrace.DCPhase(B.negate().and(C.negate())), new CounterTrace.DCPhase() });
		ct1A = compiler.compile("T7h1", ct);
		ct1A.dump();
		ct2A = compiler.compile("T7h2", ct2);
		ct2A.dump();

		ctParallel = ct1A.parallel(ct2A);
		ctParallel.dump();

		final J2UPPAALWriter j2uppaalWriter = new J2UPPAALWriter();
		j2uppaalWriter.writePEA2UppaalFile("AmiTest.xml", ctParallel);

	}

	// Test konsistente Anforderungen
	// 1) Wenn IgnitionOn dann soll sp�testens 10Sek sp�ter der MotorAn sein
	// 2) Wenn MotorAn wird dann soll fr�hestens 10Sek sp�ter das RadioAn geschaltet werden k�nnen
	// 1) CE: neg(true; event(IgnitionOn) & neg(MotorOn) & l>10; true)
	// 2) CE: neg(true; event(MotorAn) & l<10; RadioAn; true)
	public void runConsistentEx() {
		final CDD IgnitionOn = BooleanDecision.create("IgnitionOn");
		final CDD MotorOn = BooleanDecision.create("MotorOn");
		final CDD MotorOnEv = EventDecision.create("MotorOnEvent");
		final CDD RadioOn = BooleanDecision.create("RadioOn");

		PhaseEventAutomata ctParallel, ct1A, ct2A, ct3A;

		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(IgnitionOn.and(MotorOn.negate()), MotorOn.negate(), CounterTrace.BOUND_GREATER,
		                10),
		        new CounterTrace.DCPhase() });
		ct1A = compiler.compile("TIgnition", ct);
		ct1A.dump();

		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(MotorOnEv, CDD.TRUE, CounterTrace.BOUND_LESS, 10),
		        new CounterTrace.DCPhase(RadioOn), new CounterTrace.DCPhase() });
		ct2A = compiler.compile("TRadio", ct2);
		ct2A.dump();

		final CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(MotorOnEv, MotorOn.negate()), new CounterTrace.DCPhase() });
		ct3A = compiler.compile("TMEvent", ct3);
		ct3A.dump();

		ctParallel = ct1A.parallel(ct2A).parallel(ct3A);
		ctParallel.dump();

	}

	// T inkonsistente Anforderungen
	// A --> G(neg(B))
	// A --> G(B))
	// F(A)
	public void runInconsistentTest() {
		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		PhaseEventAutomata ctParallel, ct1A, ct2A, ct3A;

		// counterexample f�r A--> G(neg(B))
		final CounterTrace ct = new CounterTrace(
		        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(A),
		                new CounterTrace.DCPhase(), new CounterTrace.DCPhase(B), new CounterTrace.DCPhase() });
		ct1A = compiler.compile("Ta", ct);
		ct1A.dump();
		// counterexample f�r A--> G(B)
		final CounterTrace ct2 = new CounterTrace(
		        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(A),
		                new CounterTrace.DCPhase(), new CounterTrace.DCPhase(B.negate()), new CounterTrace.DCPhase() });
		ct2A = compiler.compile("Tb", ct2);
		ct2A.dump();

		final CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(A.negate()) });
		ct3A = compiler.compile("TMEvent", ct3);
		ct3A.dump();

		ctParallel = ct1A.parallel(ct2A).parallel(ct3A);
		ctParallel.dump();

	}

	public void run() {
		final PhaseEventAutomata ctParallel, ct1A, ct2A;
		// runTest1();
		// runTest2();
		// runTest3();
		// runTest4();
		// runTest5();
		runTest5b();
		// runTest6();
		// CDD P = BooleanDecision.create("A");
		// CDD Q = BooleanDecision.create("B");
		// ct1A = runTest7c(P, Q);
		// ct2A = runTest7c(P, Q.negate());
		// ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();
		// runTest7h();
		// runTest5c();
		// runConsistentEx();
		// runInconsistentTest();
		runTestSeeping();
		runTestTrue();
		runTestVacuous();
		runTestVacuous2();
	}

	public static void main(final String[] param) {
		new TestCase().run();
	}
}
