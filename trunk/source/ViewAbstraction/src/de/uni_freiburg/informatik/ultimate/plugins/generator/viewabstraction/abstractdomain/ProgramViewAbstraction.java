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
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.abstractdomain;

import static java.util.stream.Collectors.groupingBy;
import static java.util.stream.Collectors.mapping;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramConfiguration;

public class ProgramViewAbstraction<C, T>
		implements IViewAbstraction<ProgramConfiguration<C, T>, ProgramConfiguration<C, T>> {
	private final IViewAbstraction<Configuration<T>, Configuration<T>> mThreadViewAbstraction =
			new SimpleViewAbstraction<>();

	@Override
	public Set<ProgramConfiguration<C, T>> abstractAsViews(final ProgramConfiguration<C, T> config,
			final int viewSize) {
		return mThreadViewAbstraction.abstractAsViews(config.getThreadConfiguration(), viewSize).stream()
				.map(t -> new ProgramConfiguration<>(config.getControllerState(), t)).collect(Collectors.toSet());
	}

	@Override
	public Set<ProgramConfiguration<C, T>> concretizeFromViews(final Set<ProgramConfiguration<C, T>> views,
			final int viewSize, final int configSize) {
		final var viewsByController = views.stream().collect(groupingBy(v -> v.getControllerState(),
				mapping(v -> v.getThreadConfiguration(), Collectors.toCollection(LinkedHashSet::new))));

		final var result = new LinkedHashSet<ProgramConfiguration<C, T>>();
		for (final var entry : viewsByController.entrySet()) {
			final var controller = entry.getKey();
			final var threads = entry.getValue();
			final var concretizedThreadConfigs =
					mThreadViewAbstraction.concretizeFromViews(threads, viewSize, configSize);
			for (final var concretizedConfig : concretizedThreadConfigs) {
				result.add(new ProgramConfiguration<>(controller, concretizedConfig));
			}
		}
		return result;
	}
}
