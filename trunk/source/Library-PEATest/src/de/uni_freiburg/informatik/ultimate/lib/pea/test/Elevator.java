package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.TimedAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;

/**
 * Class to create an automaton from a counter example trace.
 *
 */
public class Elevator {
	CDD open = BooleanDecision.create("open");
	CDD close = open.negate();

	CDD dirup = BooleanDecision.create("dirup");
	CDD dirdown = dirup.negate();

	CDD reqset = RangeDecision.create("reqset", RangeDecision.OP_NEQ, 0);
	CDD dsev = EventDecision.create("doorSensor");
	CDD passedev = EventDecision.create("passed");
	Set<String> ds = Collections.singleton("doorSensor");
	Set<String> passed = Collections.singleton("passed");
	Set<String> stop = Collections.singleton("stop");
	CDD floorInReqset;

	static int minFloor = 0;
	static int maxFloor = 2;

	PhaseEventAutomata csppart, zpart, dcpart;

	public Elevator() {
		int floor, rs;
		floorInReqset = CDD.FALSE;
		for (floor = minFloor; floor <= maxFloor; floor++) {
			for (rs = 0; rs < (1 << (maxFloor - minFloor + 1)); rs++) {
				if ((rs & (1 << (floor - minFloor))) != 0) {
					floorInReqset = floorInReqset.or(RangeDecision.create("floor", RangeDecision.OP_EQ, floor)
					        .and(RangeDecision.create("reqset", RangeDecision.OP_EQ, rs)));
				}
			}
		}
	}

	public static void main(final String[] param) {
		final Elevator elev = new Elevator();

		elev.buildZPart();
		elev.buildCSPPart();
		elev.buildDCPart();

		// elev.csppart.dump();
		// elev.zpart.dump();
		// elev.dcpart.dump();
		final PhaseEventAutomata all = elev.csppart.parallel(elev.zpart).parallel(elev.dcpart);

		// elev.csppart.parallel(elev.zpart).dump();
		all.dump();

		final CDD outOfRange = RangeDecision.create("floor", RangeDecision.OP_LT, minFloor)
		        .or(RangeDecision.create("floor", RangeDecision.OP_GT, maxFloor));

		new TimedAutomata(all, new CDD[] { outOfRange }, new String[] { "OutOfRange" });
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

	private static final int getPhaseNr(final int rs, final int floor, final int dir, final int doors) {
		return ((rs * (maxFloor - minFloor + 3) + floor - minFloor + 1) * 2 + dir) * 2 + doors;
	}

	public void buildZPart() {
		final Phase[] phases = new Phase[(maxFloor - minFloor + 3) * 2 * 2 << (maxFloor - minFloor + 1)];
		Phase[] initPhases;
		int floor, rs, dir, doors;
		int phasenr, destnr;
		CDD inv1, inv2, inv3, inv4;

		final String[] noresets = new String[0];
		final CDD noevents = EventDecision.createNeg("openDoor").and(EventDecision.createNeg("closeDoor"))
		        .and(EventDecision.createNeg("request")).and(EventDecision.createNeg("passed"))
		        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("up"))
		        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("stop"));

		for (rs = 0; rs < (1 << (maxFloor - minFloor + 1)); rs++) {
			inv1 = RangeDecision.create("reqset", RangeDecision.OP_EQ, rs);

			for (floor = minFloor - 1; floor <= maxFloor + 1; floor++) {
				if (floor < minFloor) {
					inv2 = inv1.and(RangeDecision.create("floor", RangeDecision.OP_LT, minFloor));
				} else if (floor > maxFloor) {
					inv2 = inv1.and(RangeDecision.create("floor", RangeDecision.OP_GT, maxFloor));
				} else {
					inv2 = inv1.and(RangeDecision.create("floor", RangeDecision.OP_EQ, floor));
				}

				for (dir = 0; dir < 2; dir++) {
					inv3 = inv2.and(dir == 0 ? dirdown : dirup);
					for (doors = 0; doors < 2; doors++) {
						inv4 = inv3.and(doors == 0 ? close : open);
						phasenr = getPhaseNr(rs, floor, dir, doors);
						phases[phasenr] = new Phase("p" + rs + "_" + (floor + 1) + dir + doors, inv4, CDD.TRUE);
						phases[phasenr].addTransition(phases[phasenr], noevents, noresets);
					}
				}
			}
		}
		initPhases = new Phase[] { phases[getPhaseNr(0, 0, 0, 1)], phases[getPhaseNr(0, 0, 1, 1)] };

		for (rs = 0; rs < (1 << (maxFloor - minFloor + 1)); rs++) {
			for (floor = minFloor - 1; floor <= maxFloor + 1; floor++) {
				for (dir = 0; dir < 2; dir++) {
					for (doors = 0; doors < 2; doors++) {
						phasenr = getPhaseNr(rs, floor, dir, doors);

						CDD event = EventDecision.createNeg("openDoor").and(EventDecision.createNeg("closeDoor"))
						        .and(EventDecision.create("request")).and(EventDecision.createNeg("passed"))
						        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("up"))
						        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("stop"));

						for (int f = minFloor; f <= maxFloor; f++) {
							destnr = getPhaseNr(rs | (1 << (f - minFloor)), floor, dir, doors);
							if (doors == 1 && floor == f) {
								destnr = phasenr;
							}
							phases[phasenr].addTransition(phases[destnr], event, noresets);
						}

						event = EventDecision.create("openDoor").and(EventDecision.createNeg("closeDoor"))
						        .and(EventDecision.createNeg("request")).and(EventDecision.createNeg("passed"))
						        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("up"))
						        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("stop"));

						destnr = getPhaseNr(rs & ~(1 << (floor - minFloor)), floor, dir, 1);
						phases[phasenr].addTransition(phases[destnr], event, noresets);
						event = EventDecision.createNeg("openDoor").and(EventDecision.create("closeDoor"))
						        .and(EventDecision.createNeg("request")).and(EventDecision.createNeg("passed"))
						        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("up"))
						        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("stop"));

						if ((rs & ~(1 << (floor - minFloor))) != 0) {
							final boolean candown = (rs & ((1 << (floor - minFloor)) - 1)) != 0;
							final boolean canup = (rs & ~((1 << (floor + 1 - minFloor)) - 1)) != 0;
							int newdir;
							if (dir == 0 && candown) {
								newdir = 0;
							} else if (dir == 1 && canup) {
								newdir = 1;
							} else {
								newdir = 1 - dir;
							}

							destnr = getPhaseNr(rs, floor, newdir, 0);
							phases[phasenr].addTransition(phases[destnr], event, noresets);
						}
						event = EventDecision.createNeg("openDoor").and(EventDecision.createNeg("closeDoor"))
						        .and(EventDecision.createNeg("request")).and(EventDecision.create("passed"))
						        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("up"))
						        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("stop"));

						destnr = getPhaseNr(rs, floor + 1, dir, 1);
						if (floor > maxFloor) {
							destnr = phasenr;
						}
						phases[phasenr].addTransition(phases[destnr], event, noresets);

						if (floor < minFloor) {
							phases[phasenr].addTransition(phases[phasenr], event, noresets);
						}

						event = EventDecision.createNeg("openDoor").and(EventDecision.createNeg("closeDoor"))
						        .and(EventDecision.createNeg("request")).and(EventDecision.createNeg("passed"))
						        .and(EventDecision.create("showFloor")).and(EventDecision.createNeg("up"))
						        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("stop"));

						phases[phasenr].addTransition(phases[phasenr], event, noresets);
						event = EventDecision.createNeg("openDoor").and(EventDecision.createNeg("closeDoor"))
						        .and(EventDecision.createNeg("request")).and(EventDecision.createNeg("passed"))
						        .and(EventDecision.createNeg("showFloor")).and(EventDecision.create("up"))
						        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("stop"));
						if (dir == 1) {
							phases[phasenr].addTransition(phases[phasenr], event, noresets);
						}

						event = EventDecision.createNeg("openDoor").and(EventDecision.createNeg("closeDoor"))
						        .and(EventDecision.createNeg("request")).and(EventDecision.createNeg("passed"))
						        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("up"))
						        .and(EventDecision.create("down")).and(EventDecision.createNeg("stop"));
						if (dir == 0) {
							phases[phasenr].addTransition(phases[phasenr], event, noresets);
						}

						event = EventDecision.createNeg("openDoor").and(EventDecision.createNeg("closeDoor"))
						        .and(EventDecision.createNeg("request")).and(EventDecision.createNeg("passed"))
						        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("up"))
						        .and(EventDecision.createNeg("down")).and(EventDecision.create("stop"));
						if ((rs & (1 << (floor - minFloor))) != 0) {
							phases[phasenr].addTransition(phases[phasenr], event, noresets);
						}

					}
				}
			}
		}

		zpart = new PhaseEventAutomata("ZPart", phases, initPhases);
	}

	public void buildCSPPart() {
		final String[] noresets = new String[0];
		final Phase[] p = new Phase[] { new Phase("c0", CDD.TRUE, CDD.TRUE), new Phase("c1", CDD.TRUE, CDD.TRUE),
		        new Phase("c2", CDD.TRUE, CDD.TRUE), new Phase("c3", CDD.TRUE, CDD.TRUE),
		        new Phase("c4", CDD.TRUE, CDD.TRUE) };
		CDD ev;
		for (int i = 0; i < 5; i++) {
			ev = EventDecision.createNeg("closeDoor").and(EventDecision.createNeg("up"))
			        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("passed"))
			        .and(EventDecision.createNeg("stop")).and(EventDecision.createNeg("showFloor"))
			        .and(EventDecision.createNeg("openDoor"));

			p[i].addTransition(p[i], ev, noresets);
		}

		ev = EventDecision.create("closeDoor").and(EventDecision.createNeg("up"))
		        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("passed"))
		        .and(EventDecision.createNeg("stop")).and(EventDecision.createNeg("showFloor"))
		        .and(EventDecision.createNeg("openDoor"));

		p[0].addTransition(p[1], ev, noresets);

		ev = EventDecision.createNeg("closeDoor")
		        .and(EventDecision.create("up").and(EventDecision.createNeg("down"))
		                .or(EventDecision.create("down").and(EventDecision.createNeg("up"))))
		        .and(EventDecision.createNeg("passed")).and(EventDecision.createNeg("stop"))
		        .and(EventDecision.createNeg("showFloor")).and(EventDecision.createNeg("openDoor"));
		p[1].addTransition(p[2], ev, noresets);

		ev = EventDecision.createNeg("closeDoor").and(EventDecision.createNeg("up"))
		        .and(EventDecision.createNeg("down")).and(EventDecision.create("passed"))
		        .and(EventDecision.createNeg("stop")).and(EventDecision.createNeg("showFloor"))
		        .and(EventDecision.createNeg("openDoor"));
		p[2].addTransition(p[3], ev, noresets);
		ev = EventDecision.createNeg("closeDoor").and(EventDecision.createNeg("up"))
		        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("passed"))
		        .and(EventDecision.create("stop")).and(EventDecision.createNeg("showFloor"))
		        .and(EventDecision.createNeg("openDoor"));
		p[2].addTransition(p[4], ev, noresets);
		ev = EventDecision.createNeg("closeDoor").and(EventDecision.createNeg("up"))
		        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("passed"))
		        .and(EventDecision.createNeg("stop")).and(EventDecision.create("showFloor"))
		        .and(EventDecision.createNeg("openDoor"));
		p[3].addTransition(p[2], ev, noresets);
		ev = EventDecision.createNeg("closeDoor").and(EventDecision.createNeg("up"))
		        .and(EventDecision.createNeg("down")).and(EventDecision.createNeg("passed"))
		        .and(EventDecision.createNeg("stop")).and(EventDecision.createNeg("showFloor"))
		        .and(EventDecision.create("openDoor"));
		p[4].addTransition(p[0], ev, noresets);

		csppart = new PhaseEventAutomata("CSPPart", p, new Phase[] { p[0] });
	}

	public void buildDCPart() {
		final Trace2PeaCompiler compiler = new Trace2PeaCompiler(ILogger.getLogger(""));
		PhaseEventAutomata dc1, dc2, dc3, dc4, dc5, dc6;
		dc1 = compiler.compile("DC1",
		        new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE),
		                new CounterTrace.DCPhase(close), new CounterTrace.DCPhase(open, CounterTrace.BOUND_LESS, 20),
		                new CounterTrace.DCPhase(close), new CounterTrace.DCPhase(CDD.TRUE) }));
		dc2 = compiler
		        .compile("DC2",
		                new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE),
		                        new CounterTrace.DCPhase(open),
		                        new CounterTrace.DCPhase(dsev, open, CounterTrace.BOUND_LESS, 5),
		                        new CounterTrace.DCPhase(close), new CounterTrace.DCPhase(CDD.TRUE) }));
		dc3 = compiler.compile("DC3",
		        new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE),
		                new CounterTrace.DCPhase(open, CounterTrace.BOUND_GREATEREQUAL, 15),
		                new CounterTrace.DCPhase(open, CounterTrace.BOUND_GREATEREQUAL, 5, ds),
		                new CounterTrace.DCPhase(dsev.negate(), open.and(reqset), CounterTrace.BOUND_GREATER, 1, ds),
		                new CounterTrace.DCPhase(CDD.TRUE) }));

		dc4 = compiler.compile("passed_not_too_fast",
		        new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE),
		                new CounterTrace.DCPhase(passedev, CDD.TRUE, CounterTrace.BOUND_LESS, 3),
		                new CounterTrace.DCPhase(passedev, CDD.TRUE) }));
		dc5 = compiler.compile("passed_not_too_slow", new CounterTrace(
		        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(CDD.TRUE), new CounterTrace.DCPhase(close,

		                CounterTrace.BOUND_GREATEREQUAL, 10, passed), new CounterTrace.DCPhase(CDD.TRUE) }));

		dc6 = compiler
		        .compile("stop_on_floor",
		                new CounterTrace(new CounterTrace.DCPhase[] {
		                        new CounterTrace.DCPhase(CDD.TRUE), new CounterTrace.DCPhase(close.and(floorInReqset),
		                                CounterTrace.BOUND_GREATEREQUAL, 2, stop),
		                        new CounterTrace.DCPhase(CDD.TRUE) }));
		dc1.dump();
		dc2.dump();
		dc3.dump();
		dc4.dump();
		dc5.dump();
		dc6.dump();
		dcpart = dc1.parallel(dc2).parallel(dc3).parallel(dc4).parallel(dc5).parallel(dc6);
		dcpart.dump();
	}

}
