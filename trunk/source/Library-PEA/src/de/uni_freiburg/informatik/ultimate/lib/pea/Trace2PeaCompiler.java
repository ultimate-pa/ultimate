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
public class Trace2PeaCompiler {

	private static final String FINAL = "FINAL";
	private static final String START = "START";

	private static final String DEFAULT_LOGGER = "Trace2PEACompiler";

	private ILogger mLogger = null;

	private String mName;

	private CounterTrace mCountertrace;

	private String[] mClock;

	private int mCanPossiblySeep;
	private CDD[] mKeep, mEnter, mCless, mClessEq;
	private CDD[] mCKeep, mCEnter;

	private int mLastphase;

	private final Map<PhaseBits, Phase> mAllPhases;
	private Phase[] mInit;
	private final List<PhaseBits> mTodo;

	private CDD mNoSyncEvent;
	private CDD mEntrySync, mExitSync, mMissingEvents;
	private boolean mSpec;

	/*
	 * a flag indicating whether a test automaton or a countertrace automaton has to be built. In the latter case,
	 * builtTotal is set to false.
	 */
	private boolean mBuildTotal;

	/* for ARMC export */
	private HashMap<Transition, PhaseBits> mTrans2phases;

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
	public Trace2PeaCompiler(final ILogger logger, final String loggerName) {
		mLogger = logger;

		mAllPhases = new TreeMap<>();
		mTodo = new LinkedList<>();

		mTrans2phases = new HashMap<>();
	}

	/**
	 * Initialises the Trace2PEACompiler object with the default logger.
	 */
	public Trace2PeaCompiler(final ILogger logger) {
		this(logger, Trace2PeaCompiler.DEFAULT_LOGGER);
	}

	/**
	 * @return a map from PEA transitions to its target DCPhase set
	 * @param phases
	 *            the array of DCPhases in the countertrace
	 */
	public HashMap<Transition, PhaseSet> getTrans2Phases(final DCPhase phases[]) {
		final HashMap<Transition, PhaseSet> pea2ph = new HashMap<>();
		for (final Transition t : mTrans2phases.keySet()) {
			final PhaseBits pb = mTrans2phases.get(t);
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
		mName = name;
		mCountertrace = ct;
		mBuildTotal = false;
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
		mName = name;
		mCountertrace = mcTrace.getTrace();
		mEntrySync = mcTrace.getEntrySync();
		mExitSync = mcTrace.getExitSync();
		mMissingEvents = mcTrace.getMissingEvents();
		mSpec = mcTrace.getSpec();
		mBuildTotal = true;
		return (PEATestAutomaton) buildAut();
	}

	/**
	 * Sets all attributes to initial values.
	 */
	private void resetAll() {
		mAllPhases.clear();
		mTodo.clear();
		mBuildTotal = false;
		mCanPossiblySeep = 0;
		mCEnter = null;
		mCKeep = null;
		mCless = null;
		mClessEq = null;
		mClock = null;
		mCountertrace = null;
		mEnter = null;
		mEntrySync = null;
		mExitSync = null;
		mInit = null;
		mKeep = null;
		mLastphase = 0;
		mMissingEvents = null;
		mName = null;
		mSpec = false;
		mTrans2phases = new HashMap<>();
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
		if (i > 0 && mCountertrace.getPhases()[i].isAllowEmpty()) {
			result = complete(state, i - 1).and(mCountertrace.getPhases()[i].getEntryEvents());
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
					return result.or(mCless[i].negate());
				}
				return result;
			}
			if (mCountertrace.getPhases()[i].getBoundType() < 0 && (canseep(state) & ibit) == 0
					&& (state.exactbound & ibit) == 0) {
				/*
				 * The phase has a strict upper bound. It is only complete if that bound has not yet been reached.
				 */
				return result.or(mCless[i]);
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
		mClock = new String[mCountertrace.getPhases().length];
		mKeep = new CDD[mCountertrace.getPhases().length];
		mEnter = new CDD[mCountertrace.getPhases().length];
		mCless = new CDD[mCountertrace.getPhases().length];
		mClessEq = new CDD[mCountertrace.getPhases().length];

		mCKeep = new CDD[mCountertrace.getPhases().length];
		mCEnter = new CDD[mCountertrace.getPhases().length];
		mCanPossiblySeep = 0;

		for (int p = 0; p < mCountertrace.getPhases().length; p++) {
			mCless[p] = null;
			mClessEq[p] = CDD.TRUE;

			if (mCountertrace.getPhases()[p].getBoundType() != 0) {
				mClock[p] = mName + "_X" + p;
				mCless[p] =
						RangeDecision.create(mClock[p], RangeDecision.OP_LT, mCountertrace.getPhases()[p].getBound());
				mClessEq[p] =
						RangeDecision.create(mClock[p], RangeDecision.OP_LTEQ, mCountertrace.getPhases()[p].getBound());
			}

			mKeep[p] = CDD.TRUE;
			if (mCountertrace.getPhases()[p].getForbid().size() > 0) {
				/*
				 * We can only keep the state if event is not in forbid set.
				 */
				@SuppressWarnings("unchecked")
				final Set<String> empty = Collections.EMPTY_SET;
				@SuppressWarnings("unchecked")
				final Set<String> forbid = mCountertrace.getPhases()[p].getForbid();
				final CDD atom = EventDecision.create(empty, forbid);
				mKeep[p] = mKeep[p].and(atom);
			}

			mEnter[p] = mCountertrace.getPhases()[p].getEntryEvents();
			/*
			 * determine the value of entryEvents if no event occurs (always take the second child in each boolean
			 * decision). This assumes that entryEvents only uses event decisions.
			 */
			CDD value = mCountertrace.getPhases()[p].getEntryEvents();
			while (value.getDecision() instanceof EventDecision) {
				value = value.getChilds()[1];
			}

			/*
			 * If entryEvents evaluates to true, when no event occurs, we can seep through.
			 */
			if (value == CDD.TRUE) {
				mCanPossiblySeep |= 1 << p;
			}
		}

		// If buildTotal is false, countertrace automata are built.
		// The last phase that needs to be considered is the last phase
		// that is not satisfied by an empty interval. Furthermore no events
		// may be demanded to be able to neglect the phase.
		mLastphase = mCountertrace.getPhases().length - 1;
		while (!mBuildTotal && mLastphase > 0 && mCountertrace.getPhases()[mLastphase].isAllowEmpty()
				&& (mCanPossiblySeep & 1 << mLastphase) != 0) {
			mLastphase = mLastphase - 1;
		}
		mLogger.debug("Lastphase = " + mLastphase);
	}

	/**
	 * Compute for each phase whether we can seep through from the predecessor phase.
	 */
	private final int canseep(final PhaseBits p) {
		return (p.active & ~p.waiting) << 1 & mCanPossiblySeep;
	}

	/**
	 * Precompute the CDDs further using the current state information.
	 */
	private void initTrans(final PhaseBits srcBits) {
		for (int p = 0, pbit = 1; p < mCountertrace.getPhases().length; p++, pbit += pbit) {
			/*
			 * Now calculate the condition under which we can keep the current state.
			 */
			if ((srcBits.active & pbit) != 0) {
				mCKeep[p] = mKeep[p];
				if (mCountertrace.getPhases()[p].getBoundType() < 0 && (canseep(srcBits) & pbit) == 0) {
					/*
					 * phase has < or <= bound and can't be reentered. We can only stay in this state if clock hasn't
					 * reached its maximum.
					 */
					mCKeep[p] = mCKeep[p].and(mCless[p]);
				}
			} else {
				/* phase is not active and thus can't be kept */
				mCKeep[p] = CDD.FALSE;
			}

			mCEnter[p] = p > 0 ? complete(srcBits, p - 1).and(mEnter[p]) : CDD.FALSE;
			mLogger.debug("initTrans for " + srcBits + "," + p + ": complete: " + complete(srcBits, p) + " enter: "
					+ mCEnter[p] + "  keep: " + mCKeep[p]);
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
		if (mAllPhases.containsKey(destBits)) {
			mLogger.debug("Destination phase already exists");
			dest = mAllPhases.get(destBits);
		} else {
			CDD clockInv = CDD.TRUE;
			for (int p = 0, pbit = 1; pbit <= destBits.active; p++, pbit += pbit) {
				if ((destBits.waiting & pbit) != 0
						|| mCountertrace.getPhases()[p].getBoundType() < 0 && (canseep(destBits) & pbit) == 0) {
					/*
					 * Phase invariants only apply to waiting states and states with upper bounds that cannot be
					 * reentered immediately.
					 */
					if (!mBuildTotal && p == mLastphase && mCountertrace.getPhases()[p].getBoundType() > 0
							&& (destBits.exactbound & pbit) != 0) {

						// There is a very special case in which clock invariant
						// must be strict. It only occurs, if countertrace
						// automata are built. This is indicated by
						// !this.buildTotal
						clockInv = clockInv.and(mCless[p]);

					} else {
						clockInv = clockInv.and(mClessEq[p]);
					}
				}
			}

			mLogger.debug("Creating destination phase");
			dest = new Phase(destBits.toString(), stateInv, clockInv);
			dest.phaseBits = destBits;
			mAllPhases.put(destBits, dest);
			mTodo.add(destBits);
		}
		guard = guard.assume(dest.getStateInvariant().prime());
		guard = guard.assume(src.getClockInvariant());

		mLogger.debug("Creating transition to destination phase");
		// JF: only state invariants need to be primed. So, we prime the state
		// invariants in recursiveBuildTrans.
		// Transition t = src.addTransition(dest, guard.prime(), resets);
		final Transition t = src.addTransition(dest, guard, resets);
		mTrans2phases.put(t, destBits);
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
		if (p == mCountertrace.getPhases().length) {
			// If countertrace automata are built, the phase satisfying the
			// formula is omitted. Building test automata
			// (this.buildTotal==true)
			// the phase needs to be constructed.
			if (mBuildTotal || (active & 1 << p - 1) == 0) {
				mLogger.debug("Adding new transition");
				buildNewTrans(srcBits, src, guard, stateInv, resets, new PhaseBits(active, exactbound, waiting));
			}
			return;
		}

		final int pbit = 1 << p;

		/*
		 * For each dc-phase we have three different choices: We can keep it, we can enter it, and we can seep in it.
		 */

		final boolean canseepdest = ((active & ~waiting) << 1 & mCanPossiblySeep & pbit) != 0;

		/*
		 * First we determine the condition under which phase p is not activated.
		 */
		if (canseepdest) {
			/*
			 * As we can enter this phase any time the phase predicate holds, we must make sure that the phase predicate
			 * doesn't hold in the state invariant.
			 */
			recursiveBuildTrans(srcBits, src, guard, stateInv.and(mCountertrace.getPhases()[p].getInvariant().negate()),
					resets, active, waiting, exactbound, p + 1);
		} else {
			/*
			 * Make sure that the phase can neither be kept nor entered.
			 */
			final CDD leave = guard
					.and(mCEnter[p].or(mCKeep[p]).and(mCountertrace.getPhases()[p].getInvariant().prime()).negate());
			if (leave != CDD.FALSE) {
				recursiveBuildTrans(srcBits, src, leave, stateInv, resets, active, waiting, exactbound, p + 1);
			}
		}

		/* As we activate the phase make sure that its predicate holds */
		stateInv = stateInv.and(mCountertrace.getPhases()[p].getInvariant());

		final String[] resetsPlus = new String[resets.length + 1];
		System.arraycopy(resets, 0, resetsPlus, 0, resets.length);
		resetsPlus[resets.length] = mClock[p];

		if (mCountertrace.getPhases()[p].getBoundType() > 0) {
			/*
			 * This phase has a lower bound (> or >=):
			 *
			 * If we can keep it we should do so.
			 */
			final CDD keep = guard.and(mCKeep[p]);
			if (keep != CDD.FALSE) {
				if ((srcBits.waiting & pbit) != 0) {
					/*
					 * if previous state was waiting, we can either keep waiting, or enter non-waiting state.
					 */
					recursiveBuildTrans(srcBits, src, keep.and(mCless[p]), stateInv, resets, active | pbit,
							waiting | pbit, exactbound | srcBits.exactbound & pbit, p + 1);

					recursiveBuildTrans(srcBits, src, keep.and(mCless[p].negate()), stateInv, resets, active | pbit,
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
			if (mCountertrace.getPhases()[p].getBoundType() == CounterTrace.BOUND_GREATEREQUAL) {
				final CDD enterExact = remaining.and(mCEnter[p]);
				if (enterExact != CDD.FALSE) {
					mLogger.debug("Phase " + p + " can be entered exact");
					recursiveBuildTrans(srcBits, src, enterExact, stateInv, resetsPlus, active | pbit, waiting | pbit,
							exactbound | pbit, p + 1);
				}
				enterStrict = canseepdest ? remaining.and(mCEnter[p].negate()) : CDD.FALSE;
			} else {
				enterStrict = canseepdest ? remaining : remaining.and(mCEnter[p]);
			}

			/*
			 * Lastly, we can enter it normally or seep into it.
			 */
			if (enterStrict != CDD.FALSE) {
				recursiveBuildTrans(srcBits, src, enterStrict, stateInv, resetsPlus, active | pbit, waiting | pbit,
						exactbound, p + 1);
			}
		} else if (mCountertrace.getPhases()[p].getBoundType() < 0) {
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
					if (mCountertrace.getPhases()[p].getBoundType() == CounterTrace.BOUND_LESS) {
						/*
						 * For less bounds this phase never has an exact bound.
						 */
						enterNormal = guard;
						enterExact = CDD.FALSE;
					} else {
						/*
						 * For lessequal bounds this phase has an exact bound iff all forbidden events are satisfied.
						 */
						enterNormal = guard.and(mCEnter[p].negate());
						enterExact = guard.and(mCEnter[p]);
					}
					keep = CDD.FALSE;
				} else {
					if (mCountertrace.getPhases()[p].getBoundType() == CounterTrace.BOUND_LESS) {
						enterNormal = guard.and(mCEnter[p]);
						enterExact = CDD.FALSE;
					} else {
						enterNormal = CDD.FALSE;
						enterExact = guard.and(mCEnter[p]);
					}
					keep = guard.and(mCKeep[p].and(mCEnter[p].negate()));
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
							exactbound | srcBits.exactbound & pbit, p + 1);
				}

			}
		} else {
			/*
			 * No need to care whether we keep, enter or enter early
			 */

			CDD enterKeep = guard;
			if (!canseepdest) {
				enterKeep = guard.and(mCKeep[p].or(mCEnter[p]));
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
		recursiveBuildTrans(srcBits, src, mNoSyncEvent, CDD.TRUE, new String[0], 0, 0, 0, 0);
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

		mNoSyncEvent = CDD.TRUE;
		if (mEntrySync != null) {
			mNoSyncEvent = mNoSyncEvent.and(mEntrySync.negate());
		}
		if (mExitSync != null) {
			mNoSyncEvent = mNoSyncEvent.and(mExitSync.negate());
		}

		precomputeCDDs();
		for (int i = 0; i < mCountertrace.getPhases().length; i++) {
			mCEnter[i] = mCKeep[i] = CDD.FALSE;
		}

		if (mEntrySync != null) {
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
			start = new Phase(Trace2PeaCompiler.START + "_" + mName, CDD.TRUE, CDD.TRUE);
			start.addTransition(start, mNoSyncEvent.prime(), new String[0]);
			for (int i = 0; i < mCountertrace.getPhases().length; i++) {
				if ((mCanPossiblySeep & 1 << i) == 0) {
					break;
				}

				mCEnter[i] = mEnter[i];

				if (!mCountertrace.getPhases()[i].isAllowEmpty()) {
					break;
				}
			}
			recursiveBuildTrans(initHash, start, mEntrySync.and(mExitSync.negate()), CDD.TRUE, new String[0], 0, 0, 0,
					0);

			mInit = new Phase[] { start };
			mLogger.debug("Adding transitions from start state successful");
		} else {
			mLogger.debug("Bulding initial transitions");
			final Phase dummyinit = new Phase("dummyinit", CDD.TRUE, CDD.TRUE);
			/*
			 * Special case: Initially we can enter the first phases, up to the first one that does not allowEnter or
			 * requires entry events.
			 */
			for (int i = 0; i < mCountertrace.getPhases().length; i++) {
				if ((mCanPossiblySeep & 1 << i) == 0) {
					break;
				}

				/*
				 * set cEnter[i] to TRUE instead of enter[i], as there cannot be an entry event at the start.
				 */
				mCEnter[i] = CDD.TRUE;

				if (!mCountertrace.getPhases()[i].isAllowEmpty()) {
					break;
				}
			}
			recursiveBuildTrans(initHash, dummyinit, mNoSyncEvent, CDD.TRUE, new String[0], 0, 0, 0, 0);

			final List<Transition> initTrans = dummyinit.getTransitions();
			final int initSize = initTrans.size();
			mInit = new Phase[initSize];
			for (int i = 0; i < initSize; i++) {
				final Transition trans = initTrans.get(i);
				if (trans.dest.getName().equals("st")) {
					/*
					 * If the first phase is not a true phase we need a special state to enter the garbage state "st"
					 * only if the predicate of the first phase does not hold.
					 */
					start = new Phase("stinit", mCountertrace.getPhases()[0].getInvariant().negate(), CDD.TRUE);
					start.addTransition(trans.dest, mNoSyncEvent.prime(), new String[0]);
					/* for completeness add stutter-step edge */
					start.addTransition(start, mNoSyncEvent.prime(), new String[0]);
					mInit[i] = start;
				} else {
					/*
					 * For all other states the guard of trans should already equal the state invariant, so we do not
					 * need to add an extra state
					 */
					mInit[i] = trans.dest;
				}
			}
		}

		mLogger.debug("Building automaton");
		while (!mTodo.isEmpty()) {
			final PhaseBits srcBits = mTodo.remove(0);
			final Phase src = mAllPhases.get(srcBits);
			findTrans(srcBits, src);
		}
		mLogger.debug("Automaton complete");

		final Phase[] phases = new Phase[(start != null ? 1 : 0) + mAllPhases.size() + (mExitSync != null ? 1 : 0)];

		final Phase[] finalPhases = mExitSync != null ? new Phase[1] : null;

		int phaseNr = 0;
		if (start != null) {
			phases[phaseNr++] = start;
		}
		final Iterator<Phase> iter = mAllPhases.values().iterator();
		while (iter.hasNext()) {
			phases[phaseNr++] = iter.next();
		}
		if (mExitSync != null) {
			mLogger.debug("Trying to add transitions to final state");
			phases[phaseNr++] = buildExitSyncTransitions();
			finalPhases[0] = phases[phaseNr - 1];
		}
		final ArrayList<String> peaClocks = new ArrayList<>();
		for (int i = 0; i < mClock.length; i++) {
			if (mClock[i] != null) {
				if (!mClock[i].equals("")) {
					peaClocks.add(mClock[i]);
				}
			}
		}
		final HashMap<String, String> variables = new HashMap<>();
		final HashSet<String> events = new HashSet<>();
		for (int i = 0; i < mCountertrace.getPhases().length; i++) {
			addVariables(mCountertrace.getPhases()[i].getEntryEvents(), variables, events);
			addVariables(mCountertrace.getPhases()[i].getInvariant(), variables, events);
			events.addAll(mCountertrace.getPhases()[i].getForbid());
		}

		PhaseEventAutomata pea;
		if (mExitSync != null) {
			pea = new PEATestAutomaton(mName, phases, mInit, peaClocks, finalPhases).removeUnreachableLocations();
		} else {
			pea = new PhaseEventAutomata(mName, phases, mInit, peaClocks, variables, events, null);
		}

		return pea;
	}

	private void addVariables(final CDD cdd, final HashMap<String, String> variables, final HashSet<String> events) {
		final Decision<?> dec = cdd.getDecision();
		if (dec == null) {
			// may happen for true/false phases
		} else if (dec instanceof EventDecision) {
			events.add(((EventDecision) dec).getEvent());
		} else if (dec instanceof BooleanDecision) {
			variables.put(((BooleanDecision) dec).getVar(), "bool");
		} else if (dec instanceof BoogieBooleanExpressionDecision) {
			final BoogieBooleanExpressionDecision bbedec = (BoogieBooleanExpressionDecision) dec;
			for (final Entry<String, String> entry : bbedec.getVars().entrySet()) {
				final String oldType = variables.get(entry.getKey());
				final String newType = entry.getValue();
				if (oldType != null && newType != null && !oldType.equals(entry.getValue())) {
					throw new IllegalArgumentException(mName + " Variable with conflicting type declared: "
							+ entry.getKey() + " : " + oldType + " vs. " + entry.getValue());
				}
				if (oldType != null && newType == null) {
					// ignore types hidden in nested expressions
					continue;
				}
				variables.put(entry.getKey(), newType);
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
		final Phase exit = new Phase(Trace2PeaCompiler.FINAL + "_" + mName, CDD.TRUE, CDD.TRUE);
		final String[] noResets = {};
		exit.addTransition(exit, mNoSyncEvent.prime(), noResets);

		CDD exitGuard = mExitSync;
		if (mEntrySync != null) {
			exitGuard = exitGuard.and(mEntrySync.negate());
		}

		final Iterator<PhaseBits> iter = mAllPhases.keySet().iterator();
		while (iter.hasNext()) {
			final PhaseBits pBits = iter.next();
			final Phase ph = mAllPhases.get(pBits);

			CDD guard = complete(pBits, mCountertrace.getPhases().length - 1).and(mMissingEvents);
			if (!mSpec) {
				guard = guard.negate();
			}
			if (guard != CDD.FALSE) {
				final Transition t = ph.addTransition(exit, guard.and(exitGuard).prime(), noResets);
				mTrans2phases.put(t, new PhaseBits(0, 0, 0));
			}
		}
		return exit;
	}

	/**
	 * @return Returns the entrySync.
	 */
	public CDD getEntrySync() {
		return mEntrySync;
	}

	/**
	 * @return Returns the exitSync.
	 */
	public CDD getExitSync() {
		return mExitSync;
	}

}
