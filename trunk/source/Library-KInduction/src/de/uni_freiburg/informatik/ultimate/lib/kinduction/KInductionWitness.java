/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallStack;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * What the solver's model of a satisfiable k-induction base case says about the violation: the program counter of every
 * unrolled state, and the values that {@link KInductionCounterexampleBuilder} replays the violation with.
 * <p>
 * This is plain data, read off the model in {@code KInduction.checkBase} <b>before</b> the {@code pop} that discards
 * it. Afterwards the builder needs the solver only where these values leave something open.
 *
 * <h2>Which values can be trusted</h2>
 *
 * A pc step is a whole path, and where the encoding leaves a variable unconstrained the model can pick any value, also
 * one that no concrete path produces. So the values come in two kinds:
 * <ul>
 * <li>The <b>pins</b> of a state: the values of the variables that are live at its pc, see
 * {@link PcTransitionSystem#getLiveVars(int)}. The encoding keeps exactly these, so they are the values of the path the
 * model took, and every run that is to continue the way the model did has to have them there. A variable that is not
 * live is read by no path before it is written, so its value does not matter.
 * <li>The <b>candidates</b> of a step: what the versions of a variable inside the step hold (see
 * {@link PcTransitionSystem#getVersionConstants}), what the auxiliary variables of composed edges that stand for it
 * hold (see {@link PcTransitionSystem#getAuxConstants}), and its pin at the end of the step; besides, all of the
 * step's values by sort ({@link #getStepValues}), since composing can move a value to another variable. On the path the
 * model took they are that path's values, on every other path they are arbitrary. They are only ever tried, never
 * trusted: every value the builder takes is checked by executing the letter.
 * </ul>
 * Only values of the sorts Ultimate ever asks a solver for are read - numbers, Booleans, bitvectors and floating
 * point, see {@code SmtUtils.isSortForWhichWeCanGetValues} - and only those that come back as closed literals of the
 * theories. An array has no value here: a solver may report one as a function of its model (z3's {@code as-array}),
 * which means nothing outside that model. A variable without a usable value has no pin, and a state with such a live
 * variable is not one the builder can commit to, see {@link #isFullyPinned(int)}.
 * <p>
 * {@link CallStack}'s stack pointer is read separately, because how many activations are open at a step boundary is
 * something a node of a stack-encoded procedure cannot say by itself. Nothing ever leaves it unconstrained.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class KInductionWitness {

	private final int mK;
	private final int[] mPcValues;
	/** Null exactly if the program needed no activation record, see {@link #getOpenActivations(int)}. */
	private final int[] mStackPointers;
	private final List<Map<IProgramVar, Term>> mPins;
	private final boolean[] mFullyPinned;
	private final List<Map<IProgramVar, List<Term>>> mCandidates;
	private final Map<IProgramConst, Term> mConstants;
	private final List<Map<Sort, List<Term>>> mStepValues;

	/**
	 * @param pins
	 *            per state, the value of each live variable that has a usable one
	 * @param fullyPinned
	 *            per state, whether every live variable has a usable value
	 * @param candidates
	 *            per step, the values of each variable inside it, in order of preference and without duplicates
	 * @param constants
	 *            the value of each program constant
	 */
	KInductionWitness(final int k, final int[] pcValues, final int[] stackPointers,
			final List<Map<IProgramVar, Term>> pins, final boolean[] fullyPinned,
			final List<Map<IProgramVar, List<Term>>> candidates, final Map<IProgramConst, Term> constants) {
		if (pcValues.length != k + 1) {
			throw new AssertionError("expected " + (k + 1) + " pc values, got " + pcValues.length);
		}
		if (stackPointers != null && stackPointers.length != k + 1) {
			throw new AssertionError("expected " + (k + 1) + " stack pointers, got " + stackPointers.length);
		}
		if (pins.size() != k + 1 || fullyPinned.length != k + 1 || candidates.size() != k) {
			throw new AssertionError("expected values for " + (k + 1) + " states and " + k + " steps");
		}
		mK = k;
		mPcValues = pcValues;
		mStackPointers = stackPointers;
		mPins = new ArrayList<>(pins);
		mFullyPinned = fullyPinned;
		mCandidates = new ArrayList<>(candidates);
		mConstants = constants;
		mStepValues = new ArrayList<>();
		for (final Map<IProgramVar, List<Term>> ofStep : candidates) {
			final Map<Sort, Set<Term>> bySort = new LinkedHashMap<>();
			for (final List<Term> values : ofStep.values()) {
				for (final Term value : values) {
					bySort.computeIfAbsent(value.getSort(), x -> new LinkedHashSet<>()).add(value);
				}
			}
			final Map<Sort, List<Term>> stepValues = new LinkedHashMap<>();
			bySort.forEach((sort, values) -> stepValues.put(sort, List.copyOf(values)));
			mStepValues.add(Collections.unmodifiableMap(stepValues));
		}
	}

	/** The number of unrolled steps. There are {@code k + 1} states. */
	public int getK() {
		return mK;
	}

	/** The pc in state {@code idx}, a node of the {@link PcTransitionSystem}. */
	public int getPc(final int idx) {
		return mPcValues[idx];
	}

	/**
	 * The pins of state {@code idx}: the value, as a literal term, of every variable live at its pc that the model gave
	 * a usable value. See the class javadoc.
	 */
	public Map<IProgramVar, Term> getPins(final int idx) {
		return Collections.unmodifiableMap(mPins.get(idx));
	}

	/** Whether {@link #getPins(int)} has a value for every variable that is live in state {@code idx}. */
	public boolean isFullyPinned(final int idx) {
		return mFullyPinned[idx];
	}

	/**
	 * The values to try for a variable inside the step from state {@code idx} to the next, as literal terms, most
	 * promising first. See the class javadoc.
	 */
	public Map<IProgramVar, List<Term>> getCandidates(final int idx) {
		return Collections.unmodifiableMap(mCandidates.get(idx));
	}

	/**
	 * Every value the step from state {@code idx} to the next has, by sort, without duplicates: the candidates of all
	 * variables together. A value can move between variables where transitions were composed, so this is what to try
	 * after a variable's own candidates.
	 */
	public Map<Sort, List<Term>> getStepValues(final int idx) {
		return mStepValues.get(idx);
	}

	/** The value of each program constant the model has one for, as a literal term. */
	public Map<IProgramConst, Term> getConstants() {
		return Collections.unmodifiableMap(mConstants);
	}

	/** Whether this witness knows the stack depth, i.e. whether the program has a {@link CallStack} at all. */
	public boolean knowsOpenActivations() {
		return mStackPointers != null;
	}

	/**
	 * How many activations of stack-encoded procedures are open in state {@code idx}. The stack pointer itself is
	 * not constrained to start at zero - nothing needs it to - so only the difference to the start is meaningful.
	 */
	public int getOpenActivations(final int idx) {
		if (mStackPointers == null) {
			throw new UnsupportedOperationException("this witness has no stack pointer; the program has no "
					+ "stack-encoded procedure, so every node's chain of call sites already says how many calls "
					+ "are open at it");
		}
		return mStackPointers[idx] - mStackPointers[0];
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("k=").append(mK).append(", pc sequence: ");
		for (int idx = 0; idx < mK; idx++) {
			sb.append(mPcValues[idx]).append(" -> ");
		}
		sb.append(mPcValues[mK]);
		if (mStackPointers != null) {
			sb.append(", open activations: ");
			for (int idx = 0; idx <= mK; idx++) {
				sb.append(idx == 0 ? "" : " ").append(getOpenActivations(idx));
			}
		}
		return sb.toString();
	}
}
