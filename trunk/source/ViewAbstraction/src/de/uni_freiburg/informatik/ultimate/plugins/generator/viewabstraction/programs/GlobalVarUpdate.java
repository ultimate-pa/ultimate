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

import java.util.function.UnaryOperator;
import java.util.stream.IntStream;
import java.util.stream.Stream;

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
	public Stream<TransitionProvider<ProgramConfiguration<S, T>>>
			outgoingTransitions(final ProgramConfiguration<S, T> configuration) {
		return IntStream.range(0, configuration.numberOfThreads())
				.filter(i -> configuration.getThread(i).equals(mSource))
				.mapToObj(thread -> new TransitionProvider<>(configuration, thread, this::successors));
	}

	private Stream<ProgramConfiguration<S, T>> successors(final ProgramConfiguration<S, T> configuration,
			final int thread) {
		final var controllerPred = configuration.getControllerState();
		final var controllerSucc = mGlobalUpdate.apply(controllerPred);
		if (controllerSucc == null) {
			return Stream.of();
		}

		return Stream.of(configuration.replaceController(controllerSucc).replaceThread(thread, mTarget));
	}

	@Override
	public int extensionSize() {
		return 1;
	}
}
