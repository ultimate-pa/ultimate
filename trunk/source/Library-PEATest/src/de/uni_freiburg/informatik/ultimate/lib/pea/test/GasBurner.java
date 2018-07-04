package de.uni_freiburg.informatik.ultimate.lib.pea.test;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEATestAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2ARMCConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.SimplifyPEAs;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimpleSet;

/**
 * Class to create an automaton from a counter example trace.
 *
 */
@SuppressWarnings("deprecation")
public class GasBurner {
    CDD heat  = BooleanDecision.create("heat>0");
    CDD flame = BooleanDecision.create("flame>0");
    CDD gas = BooleanDecision.create("gas>0");
    CDD idle   = BooleanDecision.create("idle>0");
    CDD purge  = BooleanDecision.create("purge>0");
    CDD ignite = BooleanDecision.create("ignite>0");
    CDD burn   = BooleanDecision.create("burn>0");
    CDD s1 = EventDecision.create("sync1");
    CDD s2 = EventDecision.create("sync2");

    static int minFloor = 0;
    static int maxFloor = 2;

    PhaseEventAutomata statemachine, flamemachine, gasmachine;
    PhaseEventAutomata dc1, dc2, dc3, dc4, dc5, dc6, dc7, dc8;
    PhaseEventAutomata leakChecker, lenChecker;
    PhaseEventAutomata all;

    public void buildState() {
	final String[] noresets = new String[0];
	Phase[] p = new Phase[] {
	    new Phase("idle", idle.and(purge.negate()).and(ignite.negate()).and(burn.negate()), CDD.TRUE),
	    new Phase("purge", purge.and(idle.negate()).and(ignite.negate()).and(burn.negate()), CDD.TRUE),
	    new Phase("ignite", ignite.and(idle.negate()).and(purge.negate()).and(burn.negate()), CDD.TRUE),
	    new Phase("burn", burn.and(idle.negate()).and(ignite.negate()).and(purge.negate()), CDD.TRUE),
	};
	for (int i = 0; i < 3; i++) {
	    p[i].addTransition(p[i], CDD.TRUE, noresets);
	}
	p[0].addTransition(p[1], heat, noresets);
	p[1].addTransition(p[2], CDD.TRUE, noresets);
	p[2].addTransition(p[3], CDD.TRUE, noresets);
	p[3].addTransition(p[0], heat.negate().or(flame.negate()), noresets);
	statemachine
	    = new PhaseEventAutomata("States", p, new Phase[] { p[0] });

	p = new Phase[] {
	    new Phase("nflame", flame.negate(), CDD.TRUE),
	    new Phase("flame", flame, CDD.TRUE)
	};
	for (int i = 0; i < 2; i++) {
	    p[i].addTransition(p[i], CDD.TRUE, noresets);
	}
	p[0].addTransition(p[1], ignite, noresets);
	p[1].addTransition(p[0], CDD.TRUE, noresets);
	flamemachine
	    = new PhaseEventAutomata("Flamer", p, new Phase[] { p[0] });

	p = new Phase[] {
	    new Phase("ngas", gas.negate(), CDD.TRUE),
	    new Phase("gas", gas, CDD.TRUE)
	};
	for (int i = 0; i < 2; i++) {
	    p[i].addTransition(p[i], CDD.TRUE, noresets);
	}
	p[0].addTransition(p[1], ignite.or(burn), noresets);
	p[1].addTransition(p[0], idle.or(purge), noresets);
	gasmachine
	    = new PhaseEventAutomata("Gaser", p, new Phase[] { p[0] });
    }

    public void buildTimings() {
	final Trace2PeaCompiler compiler = new Trace2PeaCompiler(ILogger.getLogger(""));
	dc1 = compiler.compile("Prog1",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(purge, CounterTrace.BOUND_GREATER, 3008),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
	dc2 = compiler.compile("Prog2",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(ignite, CounterTrace.BOUND_GREATER, 58),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
	dc3 = compiler.compile("Syn1",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(idle.and(heat),
				     CounterTrace.BOUND_GREATER,  8),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
	dc4 = compiler.compile("Syn2",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(burn.and(heat.negate().or(flame.negate())),
				     CounterTrace.BOUND_GREATER,  8),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
	dc5 = compiler.compile("Syn3",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(gas.and(idle.or(purge)),
				     CounterTrace.BOUND_GREATER,  8),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
	dc6 = compiler.compile("Syn4",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(gas.negate().and(ignite.or(burn)),
				     CounterTrace.BOUND_GREATER,  8),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
	/* Stability */
	dc7 = compiler.compile("Stab2",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(purge.negate()),
	    new CounterTrace.DCPhase(purge, CounterTrace.BOUND_LESSEQUAL,  3000),	    new CounterTrace.DCPhase(purge.negate()),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
	dc8 = compiler.compile("Stab3",
			     new CounterTrace(new CounterTrace.DCPhase[] {
	    new CounterTrace.DCPhase(CDD.TRUE),
	    new CounterTrace.DCPhase(ignite.negate()),
	    new CounterTrace.DCPhase(ignite, CounterTrace.BOUND_LESSEQUAL,  50),
	    new CounterTrace.DCPhase(ignite.negate()),
	    new CounterTrace.DCPhase(CDD.TRUE)
	}));
    }

    public void buildReqLeak() {
	final String[] noresets = new String[0];
	final CDD leak = flame.negate().and(gas);
	final Set<String> stopleak = new SimpleSet<>(1);
	stopleak.add("cleak");
	final CDD nosync = s1.negate().and(s2.negate());
	final CDD lteq = BooleanDecision.create("20*cleak-cell<=0");
	final CDD gteq = BooleanDecision.create("20*cleak-cell<0").negate();

	final List<String> clocks = new ArrayList<>();
	clocks.add("cell");
	clocks.add("cleak");
	    
	final Phase[] p = new Phase[] {
	    new Phase("init", CDD.TRUE, CDD.TRUE),
	    new Phase("wleak", leak, lteq),
	    new Phase("wnleak", leak.negate(), CDD.TRUE, stopleak),
	    new Phase("leak", leak, CDD.TRUE),
	    new Phase("nleak", leak.negate(), gteq, stopleak),
	    new Phase("final", CDD.TRUE, CDD.TRUE)
	};
	for (int i = 0; i < 6; i++) {
	    p[i].addTransition(p[i], nosync, noresets);
	}
	p[0].addTransition(p[1], s1.and(s2.negate()),
			   new String[] { "cleak", "cell" });
	p[0].addTransition(p[2], s1.and(s2.negate()),
			   new String[] { "cleak", "cell" });
	p[0].addTransition(p[3], s1.and(s2.negate()),
			   new String[] { "cleak", "cell" });
	p[0].addTransition(p[4], s1.and(s2.negate()),
			   new String[] { "cleak", "cell" });
	p[1].addTransition(p[2], nosync, noresets);
	p[2].addTransition(p[1], nosync, noresets);
	p[1].addTransition(p[3], nosync.and(gteq), noresets);
	p[1].addTransition(p[4], nosync.and(gteq), noresets);
	p[3].addTransition(p[4], nosync, noresets);
	p[4].addTransition(p[3], nosync, noresets);
	p[4].addTransition(p[1], nosync.and(lteq), noresets);
	p[4].addTransition(p[2], nosync.and(lteq), noresets);
	p[3].addTransition(p[5], s2.and(s1.negate()), noresets);
	p[4].addTransition(p[5], s2.and(s1.negate()).and(lteq.negate()), noresets);
	leakChecker = new PEATestAutomaton("leakcheck", p,
					   new Phase[] {p[0]},
					   clocks,
					   new Phase[] {p[5]});
    }

    public void buildReq60() {
	final String[] noresets = new String[0];
	final CDD nosync = s1.negate().and(s2.negate());
	final CDD lteq = RangeDecision.create("c", RangeDecision.OP_LTEQ, 6000);
	final CDD gteq = RangeDecision.create("c", RangeDecision.OP_GTEQ, 6000);
	final List<String> clocks = new ArrayList<>();
	clocks.add("c");
	    
	final Phase[] p = new Phase[] {
	    new Phase("init", CDD.TRUE, CDD.TRUE),
	    new Phase("wait", CDD.TRUE, lteq),
	    new Phase("finished", CDD.TRUE, CDD.TRUE),
	    new Phase("final", CDD.TRUE, CDD.TRUE)
	};
	for (int i = 0; i < 4; i++) {
	    p[i].addTransition(p[i], nosync, noresets);
	}
	p[0].addTransition(p[1], s1.and(s2.negate()),
			   new String[] { "c" });
	p[1].addTransition(p[2], nosync.and(gteq), noresets);
	p[1].addTransition(p[3], s2.and(s1.negate()).and(gteq), noresets);
	p[2].addTransition(p[3], s2.and(s1.negate()), noresets);
	lenChecker = new PEATestAutomaton("lencheck", p,
					  new Phase[] {p[0]},
					  clocks,
					  new Phase[] {p[3]});
    }

    public void build() {
	buildState();
	buildTimings();
	buildReqLeak();
	buildReq60();
	all = dc1.parallel(dc2).parallel(dc3).parallel(dc4).parallel(dc5).
	    parallel(dc6).parallel(dc7).parallel(dc8).
	    parallel(statemachine).parallel(flamemachine).parallel(gasmachine).
	    parallel(lenChecker).parallel(leakChecker);
    }

    public static void main(final String[] param) {
	final GasBurner gb = new GasBurner();

	gb.build();
	gb.lenChecker.dump();
	gb.leakChecker.dump();
	gb.all.dump();

	final PEA2ARMCConverter tcsConverter
	    = new PEA2ARMCConverter();
	final ArrayList<String> mergedVariables0 = new ArrayList<>();
	final ArrayList<String> mergedTypes0 = new ArrayList<>();

	mergedVariables0.add("heat");
	mergedVariables0.add("flame");
	mergedVariables0.add("gas");
	mergedVariables0.add("idle");
	mergedVariables0.add("purge");
	mergedVariables0.add("ignite");
	mergedVariables0.add("burn");

	final SimplifyPEAs spea = new SimplifyPEAs();
	spea.removeAllEvents(gb.all);
	gb.all = spea.mergeFinalLocations((PEATestAutomaton) gb.all,
				     SimplifyPEAs.BADSTATESTRING);
	tcsConverter.convert(gb.all,"gasburner.pl",
			     mergedVariables0,mergedTypes0,
			     false);
	
    }


}
