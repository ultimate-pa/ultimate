package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DOTWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace;

public class TestUppaalExport {

	Trace2PeaCompiler compiler = new Trace2PeaCompiler(ILogger.getLogger(""));
	CDD entry = EventDecision.create("S1");
	CDD exit = EventDecision.create("S2");
	CDD missing = CDD.TRUE;

	public PhaseEventAutomata bndInvariance(final CDD P, final CDD S, final int bound) {
		PhaseEventAutomata ctA, ctA2, mctA;
		final PhaseEventAutomata mctA2;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(S, CounterTrace.BOUND_LESS, bound),
				new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
		final MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		mctA = compiler.compile("TInvariance1", mct);
		ctA = compiler.compile("TInvariance1", ct);

		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(P.and(S.negate())), new CounterTrace.DCPhase() });

		ctA2 = compiler.compile("TInvariance2", ct2);
		ctA = ctA2.parallel(ctA);
		return ctA;
	}

	public PhaseEventAutomata bndResp_Glob(final CDD P, final CDD S, final int bound) {
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(P.and(S.negate())),
				new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, bound), new CounterTrace.DCPhase() });
		ctA = compiler.compile("TBndResp", ct);
		return ctA;

	}

	public void testUppaal() {
		PhaseEventAutomata ctParallel, ct1A, ct2A;
		final CDD P = BooleanDecision.create("P");
		final CDD S = BooleanDecision.create("S");

		ct1A = bndInvariance(P, S.negate(), 6);
		ct2A = bndResp_Glob(P, S, 10);

		ctParallel = ct1A.parallel(ct2A);

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
