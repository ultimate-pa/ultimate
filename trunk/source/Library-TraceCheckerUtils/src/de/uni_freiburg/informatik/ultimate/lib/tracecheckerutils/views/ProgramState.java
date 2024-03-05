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
