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

import java.util.ArrayDeque;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SimpleViewAbstraction<S> implements IViewAbstraction<Configuration<S>, Configuration<S>> {
	@Override
	public Set<Configuration<S>> abstractAsViews(final Configuration<S> config, final int viewSize) {

		final var queue = new ArrayDeque<Pair<ImmutableList<S>, Integer>>();
		for (int i = config.numberOfThreads() - 1; i >= viewSize - 1; --i) {
			queue.push(new Pair<ImmutableList<S>, Integer>(ImmutableList.empty(), i));
		}

		final var result = new LinkedHashSet<Configuration<S>>();
		while (!queue.isEmpty()) {
			final var current = queue.pop();
			final var list = current.getFirst();
			final int index = current.getSecond();

			if (list.size() == viewSize) {
				result.add(new Configuration<>(list));
				continue;
			}

			assert index >= 0;

			final var next = new ImmutableList<>(config.getThread(index), list);
			for (int i = index - 1; i >= viewSize - next.size() - 1; --i) {
				queue.push(new Pair<>(next, i));
			}
		}
		return result;
	}

	// TODO This is an extremely naive and inefficient implementation that is bound to cause issues later on.
	@Override
	public Set<Configuration<S>> concretizeFromViews(final Set<Configuration<S>> views, final int viewSize,
			final int configSize) {
		final var states = views.stream().flatMap(c -> c.stream()).collect(Collectors.toSet());
		return listsOfSize(states, configSize).map(Configuration::new)
				.filter(c -> views.containsAll(abstractAsViews(c, viewSize)))
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}

	private Stream<ImmutableList<S>> listsOfSize(final Set<S> elements, final int size) {
		if (size == 0) {
			return Stream.of(ImmutableList.empty());
		}
		return listsOfSize(elements, size - 1).flatMap(l -> elements.stream().map(e -> new ImmutableList<>(e, l)));
	}
}
