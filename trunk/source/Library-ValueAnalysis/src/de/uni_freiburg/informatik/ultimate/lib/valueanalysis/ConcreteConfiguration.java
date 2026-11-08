/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE ValueAnalysis Library.
 *
 * The ULTIMATE ValueAnalysis Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ValueAnalysis Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ValueAnalysis Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ValueAnalysis Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ValueAnalysis Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.valueanalysis;

import java.util.Collections;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A concrete configuration of the program: a state of the abstraction (a program location), the call stack, and the
 * values of the variables of the current procedure, of the global variables and of the program constants. A variable
 * without a value has not been assigned yet; its first read chooses one.
 * <p>
 * It also remembers how it was reached, so that a configuration at an error location yields its run. Equality and
 * hash code only take the configuration itself into account, not how it was reached, so that a search can tell
 * configurations it already visited.
 *
 * @param <L>
 *            the type of letters
 * @author Max Barth (max.barth@lmu.de)
 */
public final class ConcreteConfiguration<L> {

	/**
	 * How the letter that led to a configuration is nested.
	 */
	public enum LetterKind {
		INTERNAL, CALL, RETURN
	}

	/**
	 * A frame of the call stack: the state the call was taken from, which the return needs as hierarchical
	 * predecessor, and the valuation of the caller at the call, which the return restores.
	 */
	public record Frame(IPredicate hierarchicalPredecessor, Map<IProgramVarOrConst, IConcreteValue> callerValuation,
			Frame next) {
		public int depth() {
			return next == null ? 1 : 1 + next.depth();
		}
	}

	private final IPredicate mState;
	private final Map<IProgramVarOrConst, IConcreteValue> mValuation;
	private final Frame mCallStack;
	private final int mHash;

	private final ConcreteConfiguration<L> mPredecessor;
	private final L mLetter;
	private final LetterKind mLetterKind;
	private final int mLength;

	private ConcreteConfiguration(final IPredicate state, final Map<IProgramVarOrConst, IConcreteValue> valuation,
			final Frame callStack, final ConcreteConfiguration<L> predecessor, final L letter,
			final LetterKind letterKind) {
		mState = Objects.requireNonNull(state);
		mValuation = Collections.unmodifiableMap(valuation);
		mCallStack = callStack;
		mHash = Objects.hash(mState, mValuation, mCallStack);
		mPredecessor = predecessor;
		mLetter = letter;
		mLetterKind = letterKind;
		mLength = predecessor == null ? 0 : predecessor.mLength + 1;
	}

	/**
	 * @return a configuration in an initial state, with no variable assigned and an empty call stack
	 */
	public static <L> ConcreteConfiguration<L> initial(final IPredicate state) {
		return new ConcreteConfiguration<>(state, Collections.emptyMap(), null, null, null, null);
	}

	/**
	 * @return the configuration reached from this one by {@code letter}
	 */
	public ConcreteConfiguration<L> successor(final IPredicate state,
			final Map<IProgramVarOrConst, IConcreteValue> valuation, final Frame callStack, final L letter,
			final LetterKind letterKind) {
		return new ConcreteConfiguration<>(state, valuation, callStack, this, Objects.requireNonNull(letter),
				Objects.requireNonNull(letterKind));
	}

	public IPredicate getState() {
		return mState;
	}

	public Map<IProgramVarOrConst, IConcreteValue> getValuation() {
		return mValuation;
	}

	/**
	 * @return the innermost frame of the call stack, or null if it is empty
	 */
	public Frame getCallStack() {
		return mCallStack;
	}

	/**
	 * @return the configuration this one was reached from, or null for an initial one
	 */
	public ConcreteConfiguration<L> getPredecessor() {
		return mPredecessor;
	}

	/**
	 * @return the letter this configuration was reached by, or null for an initial one
	 */
	public L getLetter() {
		return mLetter;
	}

	public LetterKind getLetterKind() {
		return mLetterKind;
	}

	/**
	 * @return the number of letters from the initial configuration to this one
	 */
	public int getLength() {
		return mLength;
	}

	@Override
	public int hashCode() {
		return mHash;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof final ConcreteConfiguration<?> other)) {
			return false;
		}
		return mHash == other.mHash && mState.equals(other.mState) && Objects.equals(mCallStack, other.mCallStack)
				&& mValuation.equals(other.mValuation);
	}

	@Override
	public String toString() {
		return mState + " " + mValuation + (mCallStack == null ? "" : " (call depth " + mCallStack.depth() + ")");
	}
}
