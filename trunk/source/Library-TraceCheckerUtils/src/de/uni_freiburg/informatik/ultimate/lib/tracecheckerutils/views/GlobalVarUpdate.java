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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ProgramState.ControllerState;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ProgramState.ThreadState;

public class GlobalVarUpdate<S, T> implements IRule<ProgramState<S, T>> {
	private final UnaryOperator<S> mGlobalUpdate;
	private final T mSource;
	private final T mTarget;

	public GlobalVarUpdate(final T source, final T target, final UnaryOperator<S> globalUpdate) {
		mGlobalUpdate = globalUpdate;
		mSource = source;
		mTarget = target;
	}

	@Override
	public boolean isApplicable(final Configuration<ProgramState<S, T>> config) {
		for (int i = 0; i < config.size(); ++i) {
			final var state = config.get(i);
			if (state.isThreadState()) {
				final var thread = state.getThreadState();
				if (thread.equals(mSource)) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public List<Configuration<ProgramState<S, T>>> successors(final Configuration<ProgramState<S, T>> config) {
		final var result = new ArrayList<Configuration<ProgramState<S, T>>>();

		assert config.get(0).isControllerState();

		for (int i = 1; i < config.size(); ++i) {
			final var state = config.get(i);
			assert state.isThreadState();
			final var thread = state.getThreadState();
			if (thread.equals(mSource)) {
				final var succ = apply(config, i);
				if (succ != null) {
					result.add(succ);
				}
			}
		}

		return result;
	}

	private Configuration<ProgramState<S, T>> apply(final Configuration<ProgramState<S, T>> config, final int i) {
		final var controllerPred = config.get(0);
		assert controllerPred.isControllerState();

		final var controllerSucc = mGlobalUpdate.apply(controllerPred.getControllerState());
		if (controllerSucc == null) {
			return null;
		}

		final var subst = Map.<Integer, ProgramState<S, T>> of(0, new ControllerState<S, T>(controllerSucc), i,
				new ThreadState<>(mTarget));
		return config.replace(subst);
	}

	@Override
	public int extensionSize() {
		return 0;
	}
}
