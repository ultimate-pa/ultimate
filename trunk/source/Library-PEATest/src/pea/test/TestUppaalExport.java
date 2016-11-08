package pea.test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.BooleanDecision;
import pea.CDD;
import pea.CounterTrace;
import pea.EventDecision;
import pea.PhaseEventAutomata;
import pea.Trace2PEACompiler;
import pea.modelchecking.DOTWriter;
import pea.modelchecking.J2UPPAALConverter;
import pea.modelchecking.MCTrace;

public class TestUppaalExport {

	Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
	CDD entry = EventDecision.create("S1");
	// CDD entry = CDD.FALSE;
	CDD exit = EventDecision.create("S2");
	// CDD exit = CDD.TRUE;
	CDD missing = CDD.TRUE;

	public PhaseEventAutomata bndInvariance(final CDD P, final CDD S, final int bound) {
		PhaseEventAutomata ctA, ctA2, mctA;
		final PhaseEventAutomata mctA2;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(S, CounterTrace.BOUND_LESS, bound),
		        new CounterTrace.DCPhase(S.negate()),
		        // new CounterTrace.DCPhase(R),
		        new CounterTrace.DCPhase() });
		final MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		mctA = compiler.compile("TInvariance1", mct); // ctA.dump();
		ctA = compiler.compile("TInvariance1", ct); // ctA.dump();

		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(P.and(S.negate())), new CounterTrace.DCPhase() });

		ctA2 = compiler.compile("TInvariance2", ct2);
		// ctA2.dump();
		ctA = ctA2.parallel(ctA); // ctA.dump();
		return ctA;
		// return mctA;
	}

	public PhaseEventAutomata bndResp_Glob(final CDD P, final CDD S, final int bound) {
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(P.and(S.negate())),
		        new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, bound), new CounterTrace.DCPhase() });
		ctA = compiler.compile("TBndResp", ct); // ctA.dump();
		return ctA;

	}

	public void testUppaal() {
		PhaseEventAutomata ctParallel, ct1A, ct2A;
		final CDD P = BooleanDecision.create("P");
		final CDD S = BooleanDecision.create("S");

		ct1A = bndInvariance(P, S.negate(), 6);
		ct2A = bndResp_Glob(P, S, 10);

		ctParallel = ct1A.parallel(ct2A);
		ctParallel.dump();

		final DOTWriter dotwriter = new DOTWriter("C:/Deadlock.dot", ctParallel);
		dotwriter.write();

		final J2UPPAALConverter j2uppaalWriter = new J2UPPAALConverter();
		j2uppaalWriter.writePEA2UppaalFile("C:/AmiTestDeadlock.xml", ctParallel);

	}

	public void run() {
		testUppaal();
	}

	public static void main(final String[] param) {
		new TestUppaalExport().run();

	}

}
