package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Document;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAJ2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.XMLWriter;

/**
 * Implementation of Philips audio protocol in PEA + Testautomaton.
 */
public class Audio {
	private final boolean ABSTRACT = false;
	
	static final int Q = 555;
	double t = 1.0 / 17;
	int Ql = (int) (Q * (1 - t)) + 1; /* round up */
	int Qh = (int) (Q * (1 + t)); /* round down */
	
	CDD high = BooleanDecision.create("wire=high");
	CDD low = high.negate();
	CDD sendOne = EventDecision.create("s.1");
	CDD sendZero = EventDecision.create("s.0");
	CDD sendStop = EventDecision.create("s.stop");
	CDD recvOne = EventDecision.create("r.1");
	CDD recvZero = EventDecision.create("r.0");
	CDD recvStop = EventDecision.create("r.stop");
	
	PhaseEventAutomata createSender() {
		final CDD clockInv = RangeDecision.create("sclk", RangeDecision.OP_LT, 2 * Qh);
		final CDD clockIval = RangeDecision.create("sclk", RangeDecision.OP_GT, 2 * Ql)
				.and(clockInv);
		final CDD clockInv4 = RangeDecision.create("sclk", RangeDecision.OP_LT, 5 * Qh);
		final CDD clockIval4 = RangeDecision.create("sclk", RangeDecision.OP_GT, 5 * Ql)
				.and(clockInv4);
		final String[] noreset = new String[0];
		final String[] reset = new String[] { "sclk" };
		final Phase[] phases = new Phase[] {
				new Phase("1", low, CDD.TRUE),
				new Phase("2", high, clockInv),
				new Phase("3", low, clockInv),
				new Phase("4", low, clockInv),
				new Phase("5", high, clockInv),
				new Phase("6", low, clockInv4)
		};
		
		final CDD noev = sendOne.negate().and(sendZero.negate())
				.and(sendStop.negate());
		final CDD onlyOne = sendOne.and(sendZero.negate())
				.and(sendStop.negate());
		final CDD onlyZero = sendOne.negate().and(sendZero)
				.and(sendStop.negate());
		final CDD onlyStop = sendOne.negate().and(sendZero.negate())
				.and(sendStop);
		
		/* add stuttering steps */
		for (int i = 0; i < 6; i++) {
			phases[i].addTransition(phases[i], noev, noreset);
		}
		
		phases[0].addTransition(phases[3], onlyOne, reset);
		phases[1].addTransition(phases[2], clockIval.and(noev), reset);
		phases[2].addTransition(phases[1], clockIval.and(onlyZero), reset);
		phases[2].addTransition(phases[3], clockIval.and(onlyOne), reset);
		phases[2].addTransition(phases[5], clockIval.and(onlyStop), reset);
		phases[3].addTransition(phases[4], clockIval.and(noev), reset);
		phases[4].addTransition(phases[1], clockIval.and(onlyZero), reset);
		phases[4].addTransition(phases[3], clockIval.and(onlyOne), reset);
		phases[5].addTransition(phases[0], clockIval4.and(noev), noreset);
		
		return new PhaseEventAutomata("Sender", phases,
				new Phase[] { phases[0] });
	}
	
	PhaseEventAutomata createReceiver() {
		final CDD clkHigh5 = RangeDecision.create("rclk", RangeDecision.OP_LT, 5 * Qh);
		final CDD clkHigh7 = RangeDecision.create("rclk", RangeDecision.OP_LT, 7 * Qh);
		final CDD clkHigh9 = RangeDecision.create("rclk", RangeDecision.OP_LT, 9 * Qh);
		final CDD clkLow5 = RangeDecision.create("rclk", RangeDecision.OP_GT, 5 * Ql);
		final CDD clkLow7 = RangeDecision.create("rclk", RangeDecision.OP_GT, 7 * Ql);
		final CDD clkLow9 = RangeDecision.create("rclk", RangeDecision.OP_GT, 9 * Ql);
		final String[] reset = new String[] { "rclk" };
		final String[] noreset = new String[0];
		final Phase[] phases = new Phase[] {
				new Phase("a", low, CDD.TRUE),
				new Phase("b", high, CDD.TRUE),
				new Phase("c", low, clkHigh5),
				new Phase("d", low, clkHigh7),
				new Phase("e", high, CDD.TRUE),
				new Phase("f", low, clkHigh9)
		};
		
		final CDD noev = recvOne.negate().and(recvZero.negate())
				.and(recvStop.negate());
		final CDD onlyOne = recvOne.and(recvZero.negate())
				.and(recvStop.negate());
		final CDD onlyZero = recvOne.negate().and(recvZero)
				.and(recvStop.negate());
		final CDD onlyStop = recvOne.negate().and(recvZero.negate())
				.and(recvStop);
		
		/* add stuttering steps */
		for (int i = 0; i < 6; i++) {
			phases[i].addTransition(phases[i], noev, noreset);
		}
		
		phases[0].addTransition(phases[1], onlyOne, reset);
		phases[1].addTransition(phases[2], noev, noreset);
		phases[2].addTransition(phases[1], clkHigh5.and(onlyOne), reset);
		phases[2].addTransition(phases[5], clkLow5.and(onlyZero), noreset);
		phases[3].addTransition(phases[0], clkLow7.and(onlyStop), reset);
		phases[3].addTransition(phases[1], clkLow5.and(clkHigh7).and(onlyOne), reset);
		phases[3].addTransition(phases[4], clkHigh5.and(onlyZero), reset);
		phases[4].addTransition(phases[3], noev, noreset);
		phases[5].addTransition(phases[1], clkLow7.and(clkHigh9).and(onlyOne), reset);
		phases[5].addTransition(phases[4], clkHigh7.and(onlyZero), reset);
		phases[5].addTransition(phases[0], clkLow9.and(onlyStop), reset);
		
		return new PhaseEventAutomata("Receiver", phases,
				new Phase[] { phases[0] });
	}
	
	PhaseEventAutomata createTester() {
		final Phase[] phases = new Phase[] {
				new Phase("idle", CDD.TRUE, CDD.TRUE),
				new Phase("exp0", CDD.TRUE, CDD.TRUE),
				new Phase("exp1", CDD.TRUE, CDD.TRUE),
				new Phase("exps", CDD.TRUE, CDD.TRUE),
				new Phase("error", CDD.TRUE, CDD.TRUE)
		};
		
		final String[] noreset = new String[0];
		final CDD sendrecv = sendOne.and(recvOne)
				.or(sendZero.and(recvZero))
				.or(sendStop.and(recvStop));
		final CDD norecv = recvOne.or(recvZero).or(recvStop).negate();
		final CDD nosend = sendOne.or(sendZero).or(sendStop).negate();
		final CDD noev = norecv.and(nosend);
		
		/* add stuttering steps */
		for (int i = 0; i < 4; i++) {
			phases[i].addTransition(phases[i], noev, noreset);
		}
		
		phases[0].addTransition(phases[0], sendrecv, noreset);
		phases[0].addTransition(phases[1], sendZero.and(norecv), noreset);
		phases[0].addTransition(phases[2], sendOne.and(norecv), noreset);
		phases[0].addTransition(phases[3], sendStop.and(norecv), noreset);
		phases[0].addTransition(phases[4], norecv.negate().and(sendrecv.negate()), noreset);
		phases[1].addTransition(phases[0], recvZero.and(nosend), noreset);
		phases[1].addTransition(phases[4], noev.negate()
				.and(recvZero.and(nosend).negate()), noreset);
		phases[2].addTransition(phases[0], recvOne.and(nosend), noreset);
		phases[2].addTransition(phases[4], noev.negate()
				.and(recvOne.and(nosend).negate()), noreset);
		phases[3].addTransition(phases[0], recvStop.and(nosend), noreset);
		phases[3].addTransition(phases[4], noev.negate()
				.and(recvStop.and(nosend).negate()), noreset);
		phases[4].addTransition(phases[4], CDD.TRUE, noreset);
		
		return new PhaseEventAutomata("Tester", phases,
				new Phase[] { phases[0] });
	}
	
	PhaseEventAutomata create4DC(final CounterTrace ct, final String name) {
		final Trace2PeaCompiler compiler = new Trace2PeaCompiler(ILogger.getLogger(""));
		final PhaseEventAutomata pea = compiler.compile(name, new MCTrace(ct, null, null, null, false));
		return abstractAutomaton(pea, ".*st[01W]*2.*");
	}
	
	PhaseEventAutomata createDCTester() {
		CounterTrace ct;
		PhaseEventAutomata pea;
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendZero.and(recvZero.negate()), CDD.TRUE,
						CounterTrace.BOUND_GREATER, 4 * Q,
						Collections.singleton("r.0"), false),
				new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = create4DC(ct, "dca");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendOne.and(recvOne.negate()), CDD.TRUE,
						CounterTrace.BOUND_GREATER, 4 * Q,
						Collections.singleton("r.1"), false),
				new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dcb")),
				".*FINAL.*");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendStop.and(recvStop.negate()), CDD.TRUE,
						CounterTrace.BOUND_GREATER, 4 * Q,
						Collections.singleton("r.stop"), false),
				new CounterTrace.DCPhase(CDD.TRUE, CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dcc")),
				".*FINAL.*");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendZero.and(recvZero.negate()), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.singleton("r.0"), true),
				new CounterTrace.DCPhase(recvOne.or(recvStop), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dc1")),
				".*FINAL.*");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendOne.and(recvOne.negate()), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.singleton("r.1"), true),
				new CounterTrace.DCPhase(recvZero.or(recvStop), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dc2")),
				".*FINAL.*");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendStop.and(recvStop.negate()), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.singleton("r.stop"), true),
				new CounterTrace.DCPhase(recvZero.or(recvOne), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dc3")),
				".*FINAL.*");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendZero.and(recvZero.negate()), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.singleton("r.0"), false),
				new CounterTrace.DCPhase(sendZero.or(sendOne).or(sendStop),
						CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dc4")),
				".*FINAL.*");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendOne.and(recvOne.negate()), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.singleton("r.1"), false),
				new CounterTrace.DCPhase(sendZero.or(sendOne).or(sendStop),
						CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dc5")),
				".*FINAL.*");
		ct = new CounterTrace(new CounterTrace.DCPhase[] {
				new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(sendStop.and(recvStop.negate()), CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.singleton("r.stop"), false),
				new CounterTrace.DCPhase(sendZero.or(sendOne).or(sendStop),
						CDD.TRUE,
						CounterTrace.BOUND_NONE, 0,
						Collections.EMPTY_SET, true)
		});
		pea = abstractAutomaton(pea.parallel(create4DC(ct, "dc6")),
				".*FINAL.*");
		return pea;
	}
	
	PhaseEventAutomata abstractAutomaton(final PhaseEventAutomata pea,
			final String finalRegex) {
		final Phase[] init = pea.getInit();
		final Phase[] newInit = new Phase[init.length];
		int ctr = 0;
		final HashMap<Phase, Phase> newPhases = new HashMap<>();
		final List<Phase> todo = new LinkedList<>();
		
		final Phase error = new Phase("FINAL", CDD.TRUE, CDD.TRUE);
		if (ABSTRACT) {
			error.addTransition(error, CDD.TRUE, new String[0]);
		}
		newPhases.put(error, error);
		for (int i = 0; i < init.length; i++) {
			newInit[i] = new Phase(init[i].getName(),
					init[i].getStateInvariant(),
					init[i].getClockInvariant());
			if (init[i].getName().matches(finalRegex)) {
				throw new IllegalArgumentException("Error state is start state: " + init[i]);
			}
			newPhases.put(init[i], newInit[i]);
			todo.add(init[i]);
		}
		while (!todo.isEmpty()) {
			final Phase oldPhase = todo.remove(0);
			final Phase newPhase = newPhases.get(oldPhase);
			CDD errorGuard = CDD.FALSE;
			for (final Transition t : oldPhase.getTransitions()) {
				final Phase dest = t.getDest();
				if (dest.getName().matches(finalRegex)) {
					if (ABSTRACT) {
						errorGuard = errorGuard.or(t.getGuard());
					} else {
						Phase newDest = newPhases.get(dest);
						if (newDest == null) {
							String name = dest.getName();
							name = "FINAL" + (ctr++);
							newDest = new Phase(name,
									dest.getStateInvariant(),
									dest.getClockInvariant());
							newPhases.put(dest, newDest);
							todo.add(dest);
						}
						newPhase.addTransition(newDest,
								t.getGuard(),
								t.getResets());
					}
				} else {
					Phase newDest = newPhases.get(dest);
					if (newDest == null) {
						newDest = new Phase(dest.getName(),
								dest.getStateInvariant(),
								dest.getClockInvariant());
						newPhases.put(dest, newDest);
						todo.add(dest);
					}
					newPhase.addTransition(newDest,
							t.getGuard(),
							t.getResets());
				}
			}
			if (errorGuard != CDD.FALSE) {
				newPhase.addTransition(error, errorGuard, new String[0]);
			}
		}
		final Phase[] allPhases = newPhases.values().toArray(new Phase[0]);
		return new PhaseEventAutomata(pea.getName(), allPhases, newInit);
	}
	
	void run() {
		final long time0 = System.currentTimeMillis();
		final PhaseEventAutomata sendrecv =
				createSender().parallel(createReceiver());
		final long time1 = System.currentTimeMillis();
		System.err.println("Sender/Receiver build: " + (time1 - time0) + " ms");
		final PhaseEventAutomata tester = createDCTester();
		final long time2 = System.currentTimeMillis();
		System.err.println("Tester build: " + (time2 - time1) + " ms");
		final PhaseEventAutomata product = tester.parallel(sendrecv);
		final long time3 = System.currentTimeMillis();
		System.err.println("Product build: " + (time3 - time2) + " ms");
		final PhaseEventAutomata abstracted = abstractAutomaton(product,
				".*FINAL.*");
		final long time4 = System.currentTimeMillis();
		System.err.println("Abstracting: " + (time4 - time3) + " ms");
		
		final PEAJ2UPPAALConverter converter = new PEAJ2UPPAALConverter();
		final Document doc = converter.convert(new PhaseEventAutomata[] {
				abstracted });
		try {
			final XMLWriter writer = new XMLWriter();
			writer.writeXMLDocumentToFile(doc, "audio.xml");
		} catch (final IOException ex) {
			System.err.println("Can't write output file");
			ex.printStackTrace();
		}
		final long time5 = System.currentTimeMillis();
		System.err.println("Uppaal Converter: " + (time5 - time4) + " ms");
	}
	
	public static void main(final String[] param) {
		final Audio audio = new Audio();
		audio.run();
	}
}
