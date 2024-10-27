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

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

public class GlobalVarUpdate<S, T> implements IRule<ProgramConfiguration<S, T>> {
	private final UnaryOperator<S> mGlobalUpdate;
	private final T mSource;
	private final T mTarget;

	public GlobalVarUpdate(final T source, final T target, final UnaryOperator<S> globalUpdate) {
		mGlobalUpdate = globalUpdate;
		mSource = source;
		mTarget = target;
	}

	@Override
	public boolean isApplicable(final ProgramConfiguration<S, T> config) {
		for (int i = 0; i < config.numberOfThreads(); ++i) {
			final var thread = config.getThread(i);
			if (thread.equals(mSource)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public List<ProgramConfiguration<S, T>> successors(final ProgramConfiguration<S, T> config) {
		final var result = new ArrayList<ProgramConfiguration<S, T>>();

		for (int i = 0; i < config.numberOfThreads(); ++i) {
			final var thread = config.getThread(i);
			if (thread.equals(mSource)) {
				final var succ = apply(config, i);
				if (succ != null) {
					result.add(succ);
				}
			}
		}

		return result;
	}

	private ProgramConfiguration<S, T> apply(final ProgramConfiguration<S, T> config, final int i) {
		final var controllerPred = config.getControllerState();

		final var controllerSucc = mGlobalUpdate.apply(controllerPred);
		if (controllerSucc == null) {
			return null;
		}

		return config.replaceController(controllerSucc).replaceThread(i, mTarget);
	}

	@Override
	public int extensionSize() {
		return 1;
	}
}
