package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.util.ArrayList;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEATestAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2ARMCConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.SimplifyPEAs;

/**
 * Class to create an automaton from a counter example trace.
 *
 */
@SuppressWarnings("deprecation")
public class ElevatorInf {

	PhaseEventAutomata csppart, zpart, dcpart;

	public static void main(final String[] param) {
		final CDD cgless = BooleanDecision.create("current <= goal - 1");
		final CDD cgleq = BooleanDecision.create("current <= goal");
		final CDD cggeq = BooleanDecision.create("goal <= current");
		final CDD cggreater = BooleanDecision.create("goal <= current - 1");

		CDD stateInv = cgless.and(cgleq).and(cggeq.negate()).and(cggreater.negate())
		        .or(cgless.negate().and(cgleq).and(cggeq).and(cggreater.negate()))
		        .or(cgless.negate().and(cgleq.negate()).and(cggeq).and(cggreater));
		stateInv = stateInv.and(BooleanDecision.create("Min <= Max"));
		final CDD transInv = BooleanDecision.create("Min = Min'").and(BooleanDecision.create("Max = Max'"));

		final Phase invP = new Phase("inv", stateInv);
		invP.addTransition(invP, transInv, new String[0]);
		final ElevatorInf elev = new ElevatorInf();

		elev.buildZPart();
		elev.buildCSPPart();
		elev.buildDCPart();

		// elev.csppart.dump();
		// elev.zpart.dump();
		// elev.dcpart.dump();
		final PhaseEventAutomata pea = elev.csppart.parallel(elev.zpart); // .parallel(elev.dcpart);

		final Phase good = new Phase("ok", CDD.TRUE);
		final Phase bad = new Phase("FINAL", CDD.TRUE);
		good.addTransition(good, CDD.TRUE, new String[0]);
		good.addTransition(bad, /* BooleanDecision.create("Min <= current") */
		        CDD.TRUE.and(BooleanDecision.create("current <= Max")).negate(), new String[0]);
		bad.addTransition(bad, CDD.TRUE, new String[0]);
		final PEATestAutomaton tester = new PEATestAutomaton("tester", new Phase[] { good, bad }, new Phase[] { good },
		        new ArrayList<String>(), new Phase[] { bad });
		PEATestAutomaton all = tester.parallel(pea);
		all = all.parallel(new PhaseEventAutomata("inv", new Phase[] { invP }, new Phase[] { invP }));
		// all = all.parallel(tester);
		final SimplifyPEAs simplifier = new SimplifyPEAs();
		simplifier.removeAllEvents(all);
		all = simplifier.mergeFinalLocations(all, "FINAL");
		simplifier.mergeTransitions(all);

		// elev.csppart.parallel(elev.zpart).dump();
		all.dump();

		final PEA2ARMCConverter pea2armcFast = new PEA2ARMCConverter();
		final ArrayList<String> addVars = new ArrayList<>();
		final ArrayList<String> addTypes = new ArrayList<>();
		addVars.add("current");
		addVars.add("goal");
		addVars.add("dir");
		addVars.add("Min");
		addVars.add("Max");
		addTypes.add("integer");
		addTypes.add("integer");
		addTypes.add("integer");
		addTypes.add("integer");
		addTypes.add("integer");

		pea2armcFast.convert(all, "./elevator.armc", addVars, addTypes, false);

		System.err.println(all.getPhases().length + " total states.");

		// System.out.println("/* Complete System */");
		// System.out.println("#locs "+all.phases.length);
		// int trans = 0;
		// for (i = 0; i < all.phases.length; i++) {
		// trans += all.phases[i].getTransitions().size();
		// }
		// System.out.println("#trans "+trans);
		// //System.out.println("#clocks "+clocks);
		// for (i = 0; i < all.phases.length; i++)
		// dumpKronos(all.phases[i]);
	}

	public void buildZPart() {
		final CDD nnewgoal = EventDecision.createNeg("newgoal");
		final CDD nstart = EventDecision.createNeg("start");
		final CDD npassed = EventDecision.createNeg("passed");
		final CDD nstop = EventDecision.createNeg("stop");
		final CDD xicurrent = BooleanDecision.create("current' = current");
		final CDD xigoal = BooleanDecision.create("goal' = goal");
		final CDD xidir = BooleanDecision.create("dir' = dir");
		final CDD stutter = nnewgoal.and(nstart).and(npassed).and(nstop).and(xicurrent).and(xigoal).and(xidir);
		final Phase zstate = new Phase("z", CDD.TRUE);
		final Phase istate = new Phase("zi", BooleanDecision.create("Min = current"));
		final String[] noresets = new String[0];
		istate.addTransition(zstate, stutter, noresets);
		zstate.addTransition(zstate, stutter, noresets);
		zstate.addTransition(zstate,
		        nnewgoal.negate().and(nstart).and(npassed).and(nstop).and(xicurrent).and(xidir)
		                .and(BooleanDecision.create("Min <= goal'")).and(BooleanDecision.create("goal' <= Max"))
		                .and(BooleanDecision.create("current <= goal'").negate()
		                        .or(BooleanDecision.create("goal' <= current").negate())),
		        noresets);
		zstate.addTransition(zstate,
		        nstart.negate().and(nnewgoal).and(npassed).and(nstop).and(xicurrent).and(xigoal)
		                .and(BooleanDecision.create("current <= goal").or(BooleanDecision.create("dir' = -1")))
		                .and(BooleanDecision.create("goal <= current").or(BooleanDecision.create("dir' = 1"))),
		        noresets);
		zstate.addTransition(zstate,
		        npassed.negate().and(nnewgoal).and(nstart).and(nstop).and(xigoal).and(xidir)
		                .and(BooleanDecision.create("current' = current + dir").and(
		                        BooleanDecision.create("current < goal").or(BooleanDecision.create("goal < current")))),
		        noresets);
		zstate.addTransition(zstate, nstop.negate().and(nnewgoal).and(nstart).and(npassed).and(xicurrent).and(xigoal)
		        .and(xidir).and(BooleanDecision.create("current = goal")), noresets);
		zpart = new PhaseEventAutomata("ZPart", new Phase[] { istate, zstate }, new Phase[] { istate });
		zpart.dump();
	}

	public void buildCSPPart() {
		final String[] noresets = new String[0];
		final Phase[] p = new Phase[] { new Phase("c0", CDD.TRUE, CDD.TRUE), new Phase("c1", CDD.TRUE, CDD.TRUE),
		        new Phase("c2", CDD.TRUE, CDD.TRUE), };
		CDD ev;
		for (int i = 0; i < 3; i++) {
			ev = EventDecision.createNeg("newgoal").and(EventDecision.createNeg("start"))
			        .and(EventDecision.createNeg("passed")).and(EventDecision.createNeg("stop"));

			p[i].addTransition(p[i], ev, noresets);
		}

		ev = EventDecision.create("newgoal").and(EventDecision.createNeg("start"))
		        .and(EventDecision.createNeg("passed")).and(EventDecision.createNeg("stop"));

		p[0].addTransition(p[1], ev, noresets);

		ev = EventDecision.createNeg("newgoal").and(EventDecision.create("start"))
		        .and(EventDecision.createNeg("passed")).and(EventDecision.createNeg("stop"));
		p[1].addTransition(p[2], ev, noresets);

		ev = EventDecision.createNeg("newgoal").and(EventDecision.createNeg("start"))
		        .and(EventDecision.create("passed")).and(EventDecision.createNeg("stop"));
		p[2].addTransition(p[2], ev, noresets);
		ev = EventDecision.createNeg("newgoal").and(EventDecision.createNeg("start"))
		        .and(EventDecision.createNeg("passed")).and(EventDecision.create("stop"));
		p[2].addTransition(p[0], ev, noresets);
		csppart = new PhaseEventAutomata("CSPPart", p, new Phase[] { p[0] });
	}

	public void buildDCPart() {
		final CDD passed = EventDecision.create("passed");
		final CDD cgeq = BooleanDecision.create("current <= goal").and(BooleanDecision.create("goal <= current"));
		final Trace2PeaCompiler compiler = new Trace2PeaCompiler(ILogger.getLogger(""));
		PhaseEventAutomata dc1, dc2;
		dc1 = compiler.compile("passed_not_too_fast",
		        new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE),
		                new CounterTrace.DCPhase(passed, CDD.TRUE, CounterTrace.BOUND_LESSEQUAL, 3),
		                new CounterTrace.DCPhase(passed, CDD.TRUE) }));

		dc2 = compiler.compile("stop_on_floor",
		        new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE),
		                new CounterTrace.DCPhase(cgeq.negate()), new CounterTrace.DCPhase(cgeq,
		                        CounterTrace.BOUND_GREATEREQUAL, 2, Collections.singleton("stop")),
		                new CounterTrace.DCPhase(CDD.TRUE) }));
		dc1.dump();
		dc2.dump();
		dcpart = dc1.parallel(dc2);
	}

}
