package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEANet;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DOTWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverterDOM;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALWriterV4;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAJ2XMLConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class PatternToPeaTest {

	private final Trace2PeaCompiler mCompiler;
	private final ILogger mLogger;
	private final PatternToPEA mPatternToPea;

	private final CDD mEntry = EventDecision.create("S1");
	private final CDD mExit = EventDecision.create("S2");
	private final CDD mMissing = CDD.TRUE;

	public PatternToPeaTest() {
		mLogger =
				UltimateMocks.createUltimateServiceProviderMock().getLoggingService().getLogger(PatternToPeaTest.class);
		mCompiler = new Trace2PeaCompiler(mLogger);
		mPatternToPea = new PatternToPEA(mLogger);
	}

	private PhaseEventAutomata testPrecedenceVac(final String id, final CDD P, final CDD S, final CDD R) {
		PhaseEventAutomata ctA;
		final CounterTrace ct =
				new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(S.negate().and(R.negate())),
						new CounterTrace.DCPhase((P.and(R.negate())).or(S.negate().and(R.negate()))),
						new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-Test", ct); // ctA.dump();
		return ctA;
	}

	public PhaseEventAutomata deadlockCounterexample(final String id, final CDD P, final CDD S, final int bound,
			final int bound2) {
		PhaseEventAutomata ctA, ctA2;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
				// new CounterTrace.DCPhase(P.negate()),
				new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, bound),
				// new CounterTrace.DCPhase(P.negate()),
				new CounterTrace.DCPhase() });

		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_LESSEQUAL, bound2),
				new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });

		// CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
		// new CounterTrace.DCPhase(),
		// new CounterTrace.DCPhase(P, CDD.TRUE, CounterTrace.BOUND_GREATER, bound),
		// new CounterTrace.DCPhase(P),
		// new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_LESS, bound2),
		// new CounterTrace.DCPhase(P),
		// new CounterTrace.DCPhase()
		// });
		ctA = mCompiler.compile(id + "-TCounterEx", ct);
		ctA.dump();
		ctA2 = mCompiler.compile(id + "-TCounterEx2", ct2);
		ctA2.dump();
		ctA = ctA.parallel(ctA2);
		ctA.dump();
		return ctA;
	}

	public void runTest3() {
		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		final CounterTrace ct =
				new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(A, CounterTrace.BOUND_LESS, 1),
						new CounterTrace.DCPhase(B, CounterTrace.BOUND_LESSEQUAL, 2) });
		MCTrace mct = new MCTrace(ct, mEntry, mExit, mMissing, true);
		mCompiler.compile("" + "-T3", mct).dump();
		mct = new MCTrace(ct, null, mExit, mMissing, true);
		mCompiler.compile("" + "-T4", mct).dump();
	}

	public void run() {
		PhaseEventAutomata ctParallel, ct1A, ct2A, ct3A;
		final CDD P = BooleanDecision.create("P");
		final CDD S = BooleanDecision.create("S");
		final CDD T = BooleanDecision.create("T");
		final CDD R = BooleanDecision.create("R");
		final CDD Q = BooleanDecision.create("Q");

		// Zweimal sich wiedersprechende BoundedInvariance Anforderungen; Der resultierende Automat ist nur für den Fall
		// G(not(P)) erfüllbar;
		// ct1A = bndInvariance("", P, S,10);
		// ct2A = bndInvariance("", P, S.negate(),10);
		// ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();

		// Zwei sich widersprechende Anforderungen
		// P--> neg(S) gilt für mindestens 11 time units
		// P--> S gilt in höchstens 10 time units
		ct1A = mPatternToPea.bndInvariancePattern("", P, Q, R, S.negate(), 6, "Globally");
		ct2A = mPatternToPea.bndResponsePattern("", P, Q, R, S, 10, "Globally");
		// ct3A = universalityPattern("", P,Q,R,"Globally");
		ct3A = deadlockCounterexample("", P, S, 3, 10);
		ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();
		// ctParallel.dumpDot();

		ct1A = mPatternToPea.absencePattern("", P, Q, R, "Before");
		// ct1A.dump();

		ct1A = mPatternToPea.bndEntryConditionPattern("", P, Q, R, S, 100, "Globally");
		ct1A.dump();
		final DOTWriter dotwriter = new DOTWriter("D:/Globally.dot", ct1A);// ctParallel
		dotwriter.write();

		ct1A = mPatternToPea.bndEntryConditionPattern("", P, Q, R, S, 100, "After");
		dotwriter.write("D:/After.dot", ct1A);

		ct1A = mPatternToPea.bndEntryConditionPattern("", P, Q, R, S, 100, "until");
		dotwriter.write("D:/Until.dot", ct1A);

		ct1A = mPatternToPea.bndEntryConditionPattern("", P, Q, R, S, 100, "Between");
		dotwriter.write("D:/Between.dot", ct1A);

		ct1A = mPatternToPea.bndEntryConditionPattern("", P, Q, R, S, 100, "Before");
		dotwriter.write("D:/Before.dot", ct1A);

		// ct1A = responseChainPattern21("", P,Q,R,S,T,"Between");
		// ct1A = precedenceChainPattern21("", P,Q,R,S,T,"Globally");
		// ct1A.dump();

		ct1A = testPrecedenceVac("", P, S, R);
		dotwriter.write("C:/vacuous/TestPrecVac.dot", ct1A);

		ct1A = mPatternToPea.precedencePattern("", P, Q, R, S, "Between");
		ct1A.dump();

		final DOTWriter dotwriter2 = new DOTWriter("C:/minDur.dot", ct1A);
		dotwriter2.write();

		final J2UPPAALWriterV4 j2uppaalWriter = new J2UPPAALWriterV4();
		j2uppaalWriter.writePEA2UppaalFile("C:/UppaalWriterV4_neu.xml", ctParallel);

		final J2UPPAALConverter j2uppaalWr = new J2UPPAALConverter();
		j2uppaalWr.writePEA2UppaalFile("C:/UppaalConverter_neu.xml", ctParallel);

		final J2UPPAALConverterDOM j2uppaalDom = new J2UPPAALConverterDOM();
		j2uppaalDom.create("C:/UppaalConverterDOM.xml", ctParallel);

		try {
			final PEAJ2XMLConverter conv = new PEAJ2XMLConverter();

			final ArrayList<PhaseEventAutomata> peaList = new ArrayList<>();
			peaList.add(ctParallel);
			final PEANet peanet = new PEANet();
			peanet.setPeas(peaList);
			conv.convert(peanet, "AmiTest2.xml");
		} catch (final Exception e) {
			e.printStackTrace();
		}

		// CDD BatteryLow = BooleanDecision.create("BatteryLow");
		// CDD TankLow = BooleanDecision.create("TankLow");
		// CDD GeneratorOn = BooleanDecision.create("GeneratorOn");
		// ct1A = bndResp_Glob(BatteryLow, GeneratorOn, 1);
		// ct2A = bndResp_Glob(TankLow, GeneratorOn.negate(), 2);
		// ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();

		// ct1A = minDuration_Glob();
		// ct2A = maxDuration_Glob();
		// ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();

		// ct1A = periodic_Glob();
		// runTest2();
		// runTest3();
	}
}
