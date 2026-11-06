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

import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallStack;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;

/**
 * What the solver's model of a satisfiable k-induction base case says about the <em>shape</em> of the violation: the
 * program counter of every unrolled state.
 * <p>
 * This is plain data, read off the model in {@code KInduction.checkBase} <b>before</b> the {@code pop} that discards
 * it, and afterwards the only thing {@link KInductionCounterexampleBuilder} needs from the solver.
 * <p>
 * Deliberately <b>almost no variable values</b>. A pc step is a whole path, and the encoding of a step does not have to
 * agree with any single concrete path about the value a variable ends up with - where the encoding leaves a variable
 * unconstrained, the model can pick a value the concrete path would never produce. Using such values to constrain the
 * reconstruction makes it fail on perfectly good counterexamples. The pc is safe to rely on, because it is what the
 * encoding is about, and the reconstruction checks feasibility for itself anyway.
 * <p>
 * {@link CallStack}'s stack pointer is the one exception, and for a reason that does not generalise: nothing ever
 * leaves it unconstrained. Every edge either does not mention it - and it then keeps its value, since it is live
 * everywhere - or moves it by exactly one per call or return on that edge. So the model does not pick its value, the
 * path does, and a reconstruction that follows the model's value is following the path the model chose. That is what
 * tells {@link KInductionCounterexampleBuilder} how many activations are open at a step boundary, which a node of a
 * stack-encoded procedure cannot say by itself.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class KInductionWitness {

	private final int mK;
	private final int[] mPcValues;
	/**
	 * Null exactly if the program needed no activation record, see {@link #getOpenActivations(int)}.
	 */
	private final int[] mStackPointers;

	KInductionWitness(final int k, final int[] pcValues, final int[] stackPointers) {
		if (pcValues.length != k + 1) {
			throw new AssertionError("expected " + (k + 1) + " pc values, got " + pcValues.length);
		}
		if (stackPointers != null && stackPointers.length != k + 1) {
			throw new AssertionError("expected " + (k + 1) + " stack pointers, got " + stackPointers.length);
		}
		mK = k;
		mPcValues = pcValues;
		mStackPointers = stackPointers;
	}

	/**
	 * The number of unrolled steps. There are {@code k + 1} states.
	 *
	 * @return the number of unrolled steps
	 */
	public int getK() {
		return mK;
	}

	/**
	 * The pc in state {@code idx}, a node of the {@link PcTransitionSystem}.
	 *
	 * @param idx
	 *            the index of the step
	 * @return the pc in state {@code idx}, a node of the {@link PcTransitionSystem}
	 */
	public int getPc(final int idx) {
		return mPcValues[idx];
	}

	/**
	 * Whether this witness knows the stack depth, i.e. whether the program has a {@link CallStack} at all.
	 *
	 * @return whether this witness knows the stack depth
	 */
	public boolean knowsOpenActivations() {
		return mStackPointers != null;
	}

	/**
	 * How many activations of stack-encoded procedures are open in state {@code idx}. The stack pointer itself is not
	 * constrained to start at zero - nothing needs it to - so only the difference to the start is meaningful.
	 *
	 * @param idx
	 *            the index of the step
	 * @return how many activations of stack-encoded procedures are open in state {@code idx}
	 * @throws UnsupportedOperationException
	 *             if the program or the solver is outside what this class supports
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
