/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs;

import java.util.Objects;

public class ProgramConfiguration<C, T> implements IThreadBasedConfiguration<T, ProgramConfiguration<C, T>> {
	private final C mControllerState;
	private final Configuration<T> mThreadStates;

	public ProgramConfiguration(final C controllerState, final Configuration<T> threadStates) {
		mControllerState = controllerState;
		mThreadStates = threadStates;
	}

	@Override
	public int numberOfThreads() {
		return mThreadStates.numberOfThreads();
	}

	public C getControllerState() {
		return mControllerState;
	}

	@Override
	public T getThread(final int i) {
		return mThreadStates.getThread(i);
	}

	public Configuration<T> getThreadConfiguration() {
		return mThreadStates;
	}

	public ProgramConfiguration<C, T> replaceController(final C newControllerState) {
		return new ProgramConfiguration<>(newControllerState, mThreadStates);
	}

	@Override
	public ProgramConfiguration<C, T> replaceThread(final int thread, final T newThreadState) {
		return new ProgramConfiguration<>(mControllerState, mThreadStates.replaceThread(thread, newThreadState));
	}

	@Override
	public int hashCode() {
		return Objects.hash(mControllerState, mThreadStates);
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
		final ProgramConfiguration other = (ProgramConfiguration) obj;
		return Objects.equals(mControllerState, other.mControllerState)
				&& Objects.equals(mThreadStates, other.mThreadStates);
	}

	@Override
	public String toString() {
		return "(" + mControllerState + ")" + mThreadStates;
	}
}
