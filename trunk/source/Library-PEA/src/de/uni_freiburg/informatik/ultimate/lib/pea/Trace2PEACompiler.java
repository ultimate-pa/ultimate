/* $Id: Trace2PEACompiler.java 408 2009-07-17 09:54:06Z jfaber $
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace;

/**
 * This class offers functionality to construct a phase event automaton from a given countertrace or a given
 * model-checkable trace.
 * <p>
 *
 * @author Jochen Hoenicke
 * @author Roland Meyer
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace
 */
public class Trace2PEACompiler {

	private static final String FINAL = "FINAL";
	private static final String START = "START";

	private static final String DEFAULT_LOGGER = "Trace2PEACompiler";

	private ILogger mLogger = null;

	private String name;

	private CounterTrace countertrace;

	private String[] clock;

	private int canPossiblySeep;
	private CDD[] keep, enter, cless, clesseq;
	private CDD[] cKeep, cEnter;

	private int lastphase;

	private final Map<PhaseBits, Phase> allPhases;
	private Phase[] init;
	private final List<PhaseBits> todo;

	private CDD noSyncEvent;
	private CDD entrySync, exitSync, missingEvents;
	private boolean spec;

	/*
	 * a flag indicating whether a test automaton or a countertrace automaton has to be built. In the latter case,
	 * builtTotal is set to false.
	 */
	private boolean buildTotal;

	/* for ARMC export */
	private HashMap<Transition, PhaseBits> trans2phases;

	/**
	 * Initialises the Trace2PEACompiler object. Takes as parameter a string that defines the loggername for the built
	 * in log4j logger. If the string is empty, the default name <code>Trace2PEACompiler</code> is used. An application
	 * using a Trace2PEACompiler object has to make sure that the logger is initialised via
	 * <code>PropertyConfigurator.configure()</code>.
	 *
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public Trace2PEACompiler(final ILogger logger, final String loggerName) {
		mLogger = logger;

		allPhases = new TreeMap<>();
		todo = new LinkedList<>();

		trans2phases = new HashMap<>();
	}

	/**
	 * Initialises the Trace2PEACompiler object with the default logger.
	 */
	public Trace2PEACompiler(final ILogger logger) {
		this(logger, Trace2PEACompiler.DEFAULT_LOGGER);
	}

	/**
	 * @return a map from PEA transitions to its target DCPhase set
	 * @param phases
	 *            the array of DCPhases in the countertrace
	 */
	public HashMap<Transition, PhaseSet> getTrans2Phases(final DCPhase phases[]) {
		final HashMap<Transition, PhaseSet> pea2ph = new HashMap<>();
		for (final Transition t : trans2phases.keySet()) {
			final PhaseBits pb = trans2phases.get(t);
			pea2ph.put(t, pb.getPhaseSet(phases));
		}
		return pea2ph;
	}

	/**
	 * Constructs a phase event automaton named <code>name</code> from the given countertrace.
	 *
	 * @param name
	 *            The name attribute of the phase event automaton is set to <code>name</code>.
	 * @param ct
	 *            The countertrace the phase event automaton is constructed for.
	 * @return The <code>PhaseEventAutomata</code> object
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace
	 */
	public PhaseEventAutomata compile(final String name, final CounterTrace ct) {
		resetAll();
		this.name = name;
		countertrace = ct;
		buildTotal = false;
		return buildAut();
	}

	/**
	 * Constructs a phase event automaton named <code>name</code> from the given model-checkable trace.
	 *
	 * @param name
	 *            The name attribute of the phase event automaton is set to <code>name</code>.
	 * @param mcTrace
	 *            The model-checkable trace (MCTrace) the phase event automaton is constructed for.
	 * @return The <code>PhaseEventAutomata</code> object. The final state is named
	 *         <code>Trace2PEACompiler.FINAL + "_" + this.name</code>.
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace
	 */
	public PEATestAutomaton compile(final String name, final MCTrace mcTrace) {
		resetAll();
		this.name = name;
		countertrace = mcTrace.getTrace();
		entrySync = mcTrace.getEntrySync();
		exitSync = mcTrace.getExitSync();
		missingEvents = mcTrace.getMissingEvents();
		spec = mcTrace.getSpec();
		buildTotal = true;
		return (PEATestAutomaton) buildAut();
	}

	/**
	 * Sets all attributes to initial values.
	 */
	private void resetAll() {
		allPhases.clear();
		todo.clear();
		buildTotal = false;
		canPossiblySeep = 0;
		cEnter = null;
		cKeep = null;
		cless = null;
		clesseq = null;
		clock = null;
		countertrace = null;
		enter = null;
		entrySync = null;
		exitSync = null;
		init = null;
		keep = null;
		lastphase = 0;
		missingEvents = null;
		name = null;
		spec = false;
		trans2phases = new HashMap<>();
	}

	/**
	 * Return the condition when we have seen the $i$th trace element completely if we are currently in the state state.
	 *
	 * @param state
	 *            the phase bits for the current state.
	 * @param i
	 *            the number of the trace element.
	 */
	private CDD complete(final PhaseBits state, final int i) {
		CDD result;

		/*
		 * A "allowEmpty" phase can be complete if the predecessor is, the entryEvents are fulfilled and this phase
		 * matches on an empty interval.
		 */
		if (i > 0 && countertrace.phases[i].allowEmpty) {
			result = complete(state, i - 1).and(countertrace.phases[i].entryEvents);
		} else {
			result = CDD.FALSE;
		}

		final int ibit = 1 << i;
		if ((state.active & ibit) != 0) {
			if ((state.waiting & ibit) != 0) {
				/*
				 * The phase is active and waiting. It is only complete if the bound has just been reached and it is an
				 * exact bound.
				 */
				if ((state.exactbound & ibit) != 0) {
					return result.or(cless[i].negate());
				}
				return result;
			}
			if (countertrace.phases[i].boundType < 0 && (canseep(state) & ibit) == 0
					&& (state.exactbound & ibit) == 0) {
				/*
				 * The phase has a strict upper bound. It is only complete if that bound has not yet been reached.
				 */
				return result.or(cless[i]);
			}
			/*
			 * Normal case: phase is active, non-waiting, no strict upper bound.
			 */
			return CDD.TRUE;
		}
		return result;
	}

	/**
	 * Internal method to precompute most CDDs used in this automaton.
	 */
	private void precomputeCDDs() {
		clock = new String[countertrace.phases.length];
		keep = new CDD[countertrace.phases.length];
		enter = new CDD[countertrace.phases.length];
		cless = new CDD[countertrace.phases.length];
		clesseq = new CDD[countertrace.phases.length];

		cKeep = new CDD[countertrace.phases.length];
		cEnter = new CDD[countertrace.phases.length];
		canPossiblySeep = 0;

		for (int p = 0; p < countertrace.phases.length; p++) {
			cless[p] = null;
			clesseq[p] = CDD.TRUE;

			if (countertrace.phases[p].boundType != 0) {
				clock[p] = name + "_X" + p;
				cless[p] = RangeDecision.create(clock[p], RangeDecision.OP_LT, countertrace.phases[p].bound);
				clesseq[p] = RangeDecision.create(clock[p], RangeDecision.OP_LTEQ, countertrace.phases[p].bound);
			}

			keep[p] = CDD.TRUE;
			if (countertrace.phases[p].forbid.size() > 0) {
				/*
				 * We can only keep the state if event is not in forbid set.
				 */
				@SuppressWarnings("unchecked")
				final Set<String> empty = Collections.EMPTY_SET;
				@SuppressWarnings("unchecked")
				final Set<String> forbid = countertrace.phases[p].forbid;
				final CDD atom = EventDecision.create(empty, forbid);
				keep[p] = keep[p].and(atom);
			}

			enter[p] = countertrace.phases[p].entryEvents;
			/*
			 * determine the value of entryEvents if no event occurs (always take the second child in each boolean
			 * decision). This assumes that entryEvents only uses event decisions.
			 */
			CDD value = countertrace.phases[p].entryEvents;
			while (value.getDecision() instanceof EventDecision) {
				value = value.getChilds()[1];
			}

			/*
			 * If entryEvents evaluates to true, when no event occurs, we can seep through.
			 */
			if (value == CDD.TRUE) {
				canPossiblySeep |= 1 << p;
			}
		}

		// If buildTotal is false, countertrace automata are built.
		// The last phase that needs to be considered is the last phase
		// that is not satisfied by an empty interval. Furthermore no events
		// may be demanded to be able to neglect the phase.
		lastphase = countertrace.phases.length - 1;
		while (!buildTotal && lastphase > 0 && countertrace.phases[lastphase].allowEmpty
				&& (canPossiblySeep & (1 << lastphase)) != 0) {
			lastphase = lastphase - 1;
		}
		mLogger.debug("Lastphase = " + lastphase);
	}

	/**
	 * Compute for each phase whether we can seep through from the predecessor phase.
	 */
	private final int canseep(final PhaseBits p) {
		return (p.active & ~p.waiting) << 1 & canPossiblySeep;
	}

	/**
	 * Precompute the CDDs further using the current state information.
	 */
	private void initTrans(final PhaseBits srcBits) {
		for (int p = 0, pbit = 1; p < countertrace.phases.length; p++, pbit += pbit) {
			/*
			 * Now calculate the condition under which we can keep the current state.
			 */
			if ((srcBits.active & pbit) != 0) {
				cKeep[p] = keep[p];
				if (countertrace.phases[p].boundType < 0 && (canseep(srcBits) & pbit) == 0) {
					/*
					 * phase has < or <= bound and can't be reentered. We can only stay in this state if clock hasn't
					 * reached its maximum.
					 */
					cKeep[p] = cKeep[p].and(cless[p]);
				}
			} else {
				/* phase is not active and thus can't be kept */
				cKeep[p] = CDD.FALSE;
			}

			cEnter[p] = p > 0 ? complete(srcBits, p - 1).and(enter[p]) : CDD.FALSE;
			mLogger.debug("initTrans for " + srcBits + "," + p + ": complete: " + complete(srcBits, p) + " enter: "
					+ cEnter[p] + "  keep: " + cKeep[p]);
		}
	}

	/**
	 * If not present, creates a new phase according to the parameters <code>stateInv</code> and <code>destBits</code>
	 * and a transition from phase <code>src</code> to the newly created phase with guard <code>guard</code> and resets
	 * <code>resets</code>. The parameter <code>src</code> is the source phase itself.
	 *
	 * @param srcBits
	 *            Bits of source phase of the new transition
	 * @param src
	 *            Source phase of the new transition
	 * @param guard
	 *            Guard of the new transition
	 * @param stateInv
	 *            Stateinvariant of the new phase
	 * @param resets
	 *            Resets of the new Transition
	 * @param destBits
	 *            Bits of the new phase
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Transition
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseBits
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 */
	private void buildNewTrans(final PhaseBits srcBits, final Phase src, CDD guard, final CDD stateInv,
			final String[] resets, final PhaseBits destBits) {
		Phase dest;
		if (allPhases.containsKey(destBits)) {
			mLogger.debug("Destination phase already exists");
			dest = allPhases.get(destBits);
		} else {
			CDD clockInv = CDD.TRUE;
			for (int p = 0, pbit = 1; pbit <= destBits.active; p++, pbit += pbit) {
				if ((destBits.waiting & pbit) != 0
						|| (countertrace.phases[p].boundType < 0 && (canseep(destBits) & pbit) == 0)) {
					/*
					 * Phase invariants only apply to waiting states and states with upper bounds that cannot be
					 * reentered immediately.
					 */
					if (!buildTotal && p == lastphase && countertrace.phases[p].boundType > 0
							&& (destBits.exactbound & pbit) != 0) {

						// There is a very special case in which clock invariant
						// must be strict. It only occurs, if countertrace
						// automata are built. This is indicated by
						// !this.buildTotal
						clockInv = clockInv.and(cless[p]);

					} else {
						clockInv = clockInv.and(clesseq[p]);
					}
				}
			}

			mLogger.debug("Creating destination phase");
			dest = new Phase(destBits.toString(), stateInv, clockInv);
			dest.phaseBits = destBits;
			allPhases.put(destBits, dest);
			todo.add(destBits);
		}
		guard = guard.assume(dest.getStateInvariant().prime());
		guard = guard.assume(src.getClockInvariant());

		mLogger.debug("Creating transition to destination phase");
		// JF: only state invariants need to be primed. So, we prime the state
		// invariants in recursiveBuildTrans.
		// Transition t = src.addTransition(dest, guard.prime(), resets);
		final Transition t = src.addTransition(dest, guard, resets);
		trans2phases.put(t, destBits);
	}

	/**
	 * Builds up all successor states of a phase event automaton state recursively. The recursion terminates when all
	 * phases in the countertrace are handled or the stateinvariant of the successor state turns out to be false.
	 * Dependant on the <code>buildTotal</code> attribute states satisfying the formula are built or omitted.
	 *
	 * @param srcBits
	 *            Bits of the phase that initiates the recursion.
	 * @param src
	 *            The phase object that initiated the recursion.
	 * @param guard
	 *            Guard of the transition to the newly created state. Is built up during the recursion
	 * @param stateInv
	 *            State invariant of the newly created state. Is built up during the recursion.
	 * @param resets
	 *            Set of clocks that needs to be reset taking the edge to the newly created state. Is built up during
	 *            the recursion.
	 * @param active
	 *            Bit of active phases in the newly created state. Is built up during the recursion.
	 * @param waiting
	 *            Bit of waiting phases in the newly created state. Is built up during the recursion.
	 * @param exactbound
	 *            Bit of phases with exact bounds in the newly created state. Is built up during the recursion.
	 * @param p
	 *            Actual handled phase of the DC formula. Used for terminating the recursion.
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseBits
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 */
	private void recursiveBuildTrans(final PhaseBits srcBits, final Phase src, final CDD guard, CDD stateInv,
			final String[] resets, final int active, final int waiting, final int exactbound, final int p) {
		if (guard.and(stateInv.prime()) == CDD.FALSE) {
			return;
		}
		mLogger.debug("recursiveBuildTrans: " + srcBits + "->" + new PhaseBits(active, exactbound, waiting) + " (" + p
				+ ") partial guards: " + guard + " inv: " + stateInv);
		if (p == countertrace.phases.length) {
			// If countertrace automata are built, the phase satisfying the
			// formula is omitted. Building test automata
			// (this.buildTotal==true)
			// the phase needs to be constructed.
			if (buildTotal || ((active & (1 << (p - 1))) == 0)) {
				mLogger.debug("Adding new transition");
				buildNewTrans(srcBits, src, guard, stateInv, resets, new PhaseBits(active, exactbound, waiting));
			}
			return;
		}

		final int pbit = 1 << p;

		/*
		 * For each dc-phase we have three different choices: We can keep it, we can enter it, and we can seep in it.
		 */

		final boolean canseepdest = (((active & ~waiting) << 1) & canPossiblySeep & pbit) != 0;

		/*
		 * First we determine the condition under which phase p is not activated.
		 */
		if (canseepdest) {
			/*
			 * As we can enter this phase any time the phase predicate holds, we must make sure that the phase predicate
			 * doesn't hold in the state invariant.
			 */
			recursiveBuildTrans(srcBits, src, guard, stateInv.and(countertrace.phases[p].invariant.negate()), resets,
					active, waiting, exactbound, p + 1);
		} else {
			/*
			 * Make sure that the phase can neither be kept nor entered.
			 */
			final CDD leave = guard.and(cEnter[p].or(cKeep[p]).and(countertrace.phases[p].invariant.prime()).negate());
			if (leave != CDD.FALSE) {
				recursiveBuildTrans(srcBits, src, leave, stateInv, resets, active, waiting, exactbound, p + 1);
			}
		}

		/* As we activate the phase make sure that its predicate holds */
		stateInv = stateInv.and(countertrace.phases[p].invariant);

		final String[] resetsPlus = new String[resets.length + 1];
		System.arraycopy(resets, 0, resetsPlus, 0, resets.length);
		resetsPlus[resets.length] = clock[p];

		if (countertrace.phases[p].boundType > 0) {
			/*
			 * This phase has a lower bound (> or >=):
			 *
			 * If we can keep it we should do so.
			 */
			final CDD keep = guard.and(cKeep[p]);
			if (keep != CDD.FALSE) {
				if ((srcBits.waiting & pbit) != 0) {
					/*
					 * if previous state was waiting, we can either keep waiting, or enter non-waiting state.
					 */
					recursiveBuildTrans(srcBits, src, keep.and(cless[p]), stateInv, resets, active | pbit,
							waiting | pbit, exactbound | (srcBits.exactbound & pbit), p + 1);

					recursiveBuildTrans(srcBits, src, keep.and(cless[p].negate()), stateInv, resets, active | pbit,
							waiting, exactbound, p + 1);
				} else {
					/* We can keep it in non-waiting state. */
					recursiveBuildTrans(srcBits, src, keep, stateInv, resets, active | pbit, waiting, exactbound,
							p + 1);
				}
			}

			final CDD remaining = guard.and(keep.negate());
			CDD enterStrict;

			/*
			 * We must not reenter the state if we can stay in it. We must enter it through the waiting phase. If this
			 * is a greater equal phase we need to set the exactbound if we enter directly, (not via seep through rule).
			 */
			if (countertrace.phases[p].boundType == CounterTrace.BOUND_GREATEREQUAL) {
				final CDD enterExact = remaining.and(cEnter[p]);
				if (enterExact != CDD.FALSE) {
					mLogger.debug("Phase " + p + " can be entered exact");
					recursiveBuildTrans(srcBits, src, enterExact, stateInv, resetsPlus, active | pbit, waiting | pbit,
							exactbound | pbit, p + 1);
				}
				enterStrict = canseepdest ? remaining.and(cEnter[p].negate()) : CDD.FALSE;
			} else {
				enterStrict = canseepdest ? remaining : remaining.and(cEnter[p]);
			}

			/*
			 * Lastly, we can enter it normally or seep into it.
			 */
			if (enterStrict != CDD.FALSE) {
				recursiveBuildTrans(srcBits, src, enterStrict, stateInv, resetsPlus, active | pbit, waiting | pbit,
						exactbound, p + 1);
			}
		} else if (countertrace.phases[p].boundType < 0) {
			/*
			 * This phase has an upper bound ( < or <=):
			 *
			 * If we can enter it we should do so.
			 */
			if (canseepdest) {
				/*
				 * we can reenter it at any time. We need not to handle clocks.
				 */
				recursiveBuildTrans(srcBits, src, guard, stateInv, resets, active | pbit, waiting, exactbound, p + 1);
			} else {
				CDD enterNormal, enterExact, keep;

				if ((canseep(srcBits) & pbit) != 0) {
					if (countertrace.phases[p].boundType == CounterTrace.BOUND_LESS) {
						/*
						 * For less bounds this phase never has an exact bound.
						 */
						enterNormal = guard;
						enterExact = CDD.FALSE;
					} else {
						/*
						 * For lessequal bounds this phase has an exact bound iff all forbidden events are satisfied.
						 */
						enterNormal = guard.and(cEnter[p].negate());
						enterExact = guard.and(cEnter[p]);
					}
					keep = CDD.FALSE;
				} else {
					if (countertrace.phases[p].boundType == CounterTrace.BOUND_LESS) {
						enterNormal = guard.and(cEnter[p]);
						enterExact = CDD.FALSE;
					} else {
						enterNormal = CDD.FALSE;
						enterExact = guard.and(cEnter[p]);
					}
					keep = guard.and(cKeep[p].and(cEnter[p].negate()));
				}

				if (enterNormal != CDD.FALSE) {

					recursiveBuildTrans(srcBits, src, enterNormal, stateInv, resetsPlus, active | pbit, waiting,
							exactbound, p + 1);
				}
				if (enterExact != CDD.FALSE) {
					recursiveBuildTrans(srcBits, src, enterExact, stateInv, resetsPlus, active | pbit, waiting,
							exactbound | pbit, p + 1);
				}
				if (keep != CDD.FALSE) {
					recursiveBuildTrans(srcBits, src, keep, stateInv, resets, active | pbit, waiting,
							exactbound | (srcBits.exactbound & pbit), p + 1);
				}

			}
		} else {
			/*
			 * No need to care whether we keep, enter or enter early
			 */

			CDD enterKeep = guard;
			if (!canseepdest) {
				enterKeep = guard.and(cKeep[p].or(cEnter[p]));
			}
			if (enterKeep != CDD.FALSE) {
				recursiveBuildTrans(srcBits, src, enterKeep, stateInv, resets, active | pbit, waiting, exactbound,
						p + 1);
			}
		}
	}

	/**
	 * Precomputes cdds with the phase information offered by <code>srcBits</code> and afterwards initiates the
	 * recursion for finding successor states.
	 *
	 * @param srcBits
	 *            Source bits of the state initiating the recursion
	 * @param src
	 *            Source phase initiating the recursion
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseBits
	 */
	private void findTrans(final PhaseBits srcBits, final Phase src) {
		initTrans(srcBits);
		recursiveBuildTrans(srcBits, src, noSyncEvent, CDD.TRUE, new String[0], 0, 0, 0, 0);
	}

	/**
	 * Builds up the PEA test automaton that is returned by the <code>compile</code> methods. Loops all phases in the
	 * <code>todo</code> list to compute successors. Successors are also added to that list. Initially a dummy phase is
	 * used to compute the init states of the phase event automaton. If <code>buildTotal</code> bit is set further
	 * methods are called to build up a test automaton instead of a countertrace automaton.
	 * <p>
	 * In future versions of this class the attribute <code>allowEmpty</code> in <code>CounterTrace.DCPhase</code> needs
	 * to be inspected to find out, whether phases in the trace may be entered without having to use seep.
	 *
	 * @return The test automaton for the countertrace or model-checkable trace
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PEATestAutomaton
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase
	 */
	private PhaseEventAutomata buildAut() {
		final PhaseBits initHash = new PhaseBits(0, 0, 0);
		Phase start = null;

		noSyncEvent = CDD.TRUE;
		if (entrySync != null) {
			noSyncEvent = noSyncEvent.and(entrySync.negate());
		}
		if (exitSync != null) {
			noSyncEvent = noSyncEvent.and(exitSync.negate());
		}

		precomputeCDDs();
		for (int i = 0; i < countertrace.phases.length; i++) {
			cEnter[i] = cKeep[i] = CDD.FALSE;
		}

		if (entrySync != null) {
			/*
			 * Test automata method <p>
			 *
			 * Generates a new initial state which replaces all other initial states. From this state a transition to
			 * all former initial states is constructed where all clocks in the automaton are reset and the event
			 * <code>entrySync</code> is demanded, the event <code>exitSync</code> is forbidden. The method is only
			 * called if there is an entry sync. Furthermore a reflexive transition is constructed for the new state
			 * that forbids <code>entrySync</code> and <code>exitSync</code>.
			 *
			 */

			mLogger.debug("Trying to add transitions from start state");
			start = new Phase(Trace2PEACompiler.START + "_" + name, CDD.TRUE, CDD.TRUE);
			start.addTransition(start, noSyncEvent.prime(), new String[0]);
			for (int i = 0; i < countertrace.phases.length; i++) {
				if ((canPossiblySeep & (1 << i)) == 0) {
					break;
				}

				cEnter[i] = enter[i];

				if (!countertrace.phases[i].allowEmpty) {
					break;
				}
			}
			recursiveBuildTrans(initHash, start, entrySync.and(exitSync.negate()), CDD.TRUE, new String[0], 0, 0, 0, 0);

			init = new Phase[] { start };
			mLogger.debug("Adding transitions from start state successful");
		} else {
			mLogger.debug("Bulding initial transitions");
			final Phase dummyinit = new Phase("dummyinit", CDD.TRUE, CDD.TRUE);
			/*
			 * Special case: Initially we can enter the first phases, up to the first one that does not allowEnter or
			 * requires entry events.
			 */
			for (int i = 0; i < countertrace.phases.length; i++) {
				if ((canPossiblySeep & (1 << i)) == 0) {
					break;
				}

				/*
				 * set cEnter[i] to TRUE instead of enter[i], as there cannot be an entry event at the start.
				 */
				cEnter[i] = CDD.TRUE;

				if (!countertrace.phases[i].allowEmpty) {
					break;
				}
			}
			recursiveBuildTrans(initHash, dummyinit, noSyncEvent, CDD.TRUE, new String[0], 0, 0, 0, 0);

			final List<Transition> initTrans = dummyinit.getTransitions();
			final int initSize = initTrans.size();
			init = new Phase[initSize];
			for (int i = 0; i < initSize; i++) {
				final Transition trans = (initTrans.get(i));
				if (trans.dest.getName().equals("st")) {
					/*
					 * If the first phase is not a true phase we need a special state to enter the garbage state "st"
					 * only if the predicate of the first phase does not hold.
					 */
					start = new Phase("stinit", countertrace.phases[0].invariant.negate(), CDD.TRUE);
					start.addTransition(trans.dest, noSyncEvent.prime(), new String[0]);
					/* for completeness add stutter-step edge */
					start.addTransition(start, noSyncEvent.prime(), new String[0]);
					init[i] = start;
				} else {
					/*
					 * For all other states the guard of trans should already equal the state invariant, so we do not
					 * need to add an extra state
					 */
					init[i] = trans.dest;
				}
			}
		}

		mLogger.debug("Building automaton");
		while (!todo.isEmpty()) {
			final PhaseBits srcBits = todo.remove(0);
			final Phase src = allPhases.get(srcBits);
			findTrans(srcBits, src);
		}
		mLogger.debug("Automaton complete");

		final Phase[] phases = new Phase[(start != null ? 1 : 0) + allPhases.size() + (exitSync != null ? 1 : 0)];

		final Phase[] finalPhases = (exitSync != null ? new Phase[1] : null);

		int phaseNr = 0;
		if (start != null) {
			phases[phaseNr++] = start;
		}
		final Iterator<Phase> iter = allPhases.values().iterator();
		while (iter.hasNext()) {
			phases[phaseNr++] = iter.next();
		}
		if (exitSync != null) {
			mLogger.debug("Trying to add transitions to final state");
			phases[phaseNr++] = buildExitSyncTransitions();
			finalPhases[0] = phases[phaseNr - 1];
		}
		final ArrayList<String> peaClocks = new ArrayList<>();
		for (int i = 0; i < clock.length; i++) {
			if (clock[i] != null) {
				if (!clock[i].equals("")) {
					peaClocks.add(clock[i]);
				}
			}
		}
		final HashMap<String, String> variables = new HashMap<>();
		final HashSet<String> events = new HashSet<>();
		for (int i = 0; i < countertrace.phases.length; i++) {
			addVariables(countertrace.phases[i].entryEvents, variables, events);
			addVariables(countertrace.phases[i].invariant, variables, events);
			events.addAll(countertrace.phases[i].forbid);
		}

		PhaseEventAutomata pea;
		if (exitSync != null) {
			pea = new PEATestAutomaton(name, phases, init, peaClocks, finalPhases).removeUnreachableLocations();
		} else {
			pea = new PhaseEventAutomata(name, phases, init, peaClocks, variables, events, null);
		}

		return pea;
	}

	private void addVariables(final CDD cdd, final HashMap<String, String> variables, final HashSet<String> events) {
		final Decision dec = cdd.getDecision();
		if (dec == null) {
			// may happen for true/false phases
		} else if (dec instanceof EventDecision) {
			events.add(((EventDecision) dec).getEvent());
		} else if (dec instanceof BooleanDecision) {
			variables.put(((BooleanDecision) dec).getVar(), "bool");
		} else if (dec instanceof BoogieBooleanExpressionDecision) {
			final BoogieBooleanExpressionDecision bbedec = (BoogieBooleanExpressionDecision) dec;
			for (final Entry<String, String> entry : bbedec.getVars().entrySet()) {
				final String oldType = variables.put(entry.getKey(), entry.getValue());
				if (oldType != null && !oldType.equals(entry.getValue())) {
					throw new IllegalArgumentException(name + " Variable with conflicting type declared: "
							+ entry.getKey() + " : " + oldType + " vs. " + entry.getValue());
				}
			}
		} else {
			throw new UnsupportedOperationException("Unknown decision type: " + dec.getClass());
		}
		if (cdd.getChilds() != null) {
			for (final CDD child : cdd.getChilds()) {
				addVariables(child, variables, events);
			}
		}
	}

	/**
	 * Test automata method
	 * <p>
	 *
	 * Generates a new state named <code>Trace2PEACompiler.FINAL + "_" + this.name</code>. From every state in the
	 * automaton a guard is computed for a new transition to this final state. The transition depends on the
	 * <code>spec</code> attribute. If this attribute is <code>true</code> that guard states that the formula needs to
	 * be satisfied when the transition is taken and all events in the <code>missingEvents</code> cdd need to appear or
	 * may not appear as specified. When the spec is set to <code>false</code> the guard may not be satisfied or the
	 * missing events may not appear appropriately. If the guard turns out to be equivalent to false the edge to the
	 * final state is omitted. Furthermore all edges demand the <code>exitSync</code> and forbid the
	 * <code>entrySync</code>.
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace
	 */
	private Phase buildExitSyncTransitions() {
		final Phase exit = new Phase(Trace2PEACompiler.FINAL + "_" + name, CDD.TRUE, CDD.TRUE);
		final String[] noResets = {};
		exit.addTransition(exit, noSyncEvent.prime(), noResets);

		CDD exitGuard = exitSync;
		if (entrySync != null) {
			exitGuard = exitGuard.and(entrySync.negate());
		}

		final Iterator<PhaseBits> iter = allPhases.keySet().iterator();
		while (iter.hasNext()) {
			final PhaseBits pBits = iter.next();
			final Phase ph = allPhases.get(pBits);

			CDD guard = complete(pBits, countertrace.phases.length - 1).and(missingEvents);
			if (!spec) {
				guard = guard.negate();
			}
			if (guard != CDD.FALSE) {
				final Transition t = ph.addTransition(exit, guard.and(exitGuard).prime(), noResets);
				trans2phases.put(t, new PhaseBits(0, 0, 0));
			}
		}
		return exit;
	}

	/**
	 * @return Returns the entrySync.
	 */
	public CDD getEntrySync() {
		return entrySync;
	}

	/**
	 * @return Returns the exitSync.
	 */
	public CDD getExitSync() {
		return exitSync;
	}

}
