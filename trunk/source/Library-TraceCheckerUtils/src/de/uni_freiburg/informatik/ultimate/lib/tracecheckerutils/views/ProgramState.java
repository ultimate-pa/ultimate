/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.Objects;

public abstract class ProgramState<S, T> {
	private ProgramState() {
		// no subclasses except nested
	}

	public boolean isThreadState() {
		return false;
	}

	public boolean isControllerState() {
		return false;
	}

	public T getThreadState() {
		throw new AssertionError();
	}

	public S getControllerState() {
		throw new AssertionError();
	}

	public static final class ControllerState<S, T> extends ProgramState<S, T> {
		private final S mState;

		public ControllerState(final S state) {
			mState = state;
		}

		@Override
		public boolean isControllerState() {
			return true;
		}

		@Override
		public S getControllerState() {
			return mState;
		}

		@Override
		public int hashCode() {
			return Objects.hash(mState);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final ControllerState other = (ControllerState) obj;
			return Objects.equals(mState, other.mState);
		}

		@Override
		public String toString() {
			return mState.toString();
		}
	}

	public static final class ThreadState<S, T> extends ProgramState<S, T> {
		private final T mState;

		public ThreadState(final T state) {
			mState = state;
		}

		@Override
		public boolean isThreadState() {
			return true;
		}

		@Override
		public T getThreadState() {
			return mState;
		}

		@Override
		public int hashCode() {
			return Objects.hash(mState);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final ThreadState other = (ThreadState) obj;
			return Objects.equals(mState, other.mState);
		}

		@Override
		public String toString() {
			return mState.toString();
		}
	}
}
