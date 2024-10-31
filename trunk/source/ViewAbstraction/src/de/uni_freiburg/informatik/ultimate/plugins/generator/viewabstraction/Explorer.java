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
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.List;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;

public class Explorer<C> {
	private final Program<C> mProgram;
	private final List<C> mInitialConfigurations;

	public Explorer(final Program<C> program, final List<C> initialConfigurations) {
		mProgram = program;
		mInitialConfigurations = initialConfigurations;
	}

	public void dfs(final Consumer<C> consumer) {
		final var stack = new ArrayDeque<C>();
		final var visited = new HashSet<C>();
		stack.addAll(mInitialConfigurations);

		while (!stack.isEmpty()) {
			final var current = stack.pop();
			if (!visited.add(current)) {
				continue;
			}
			consumer.accept(current);

			for (final var rule : mProgram.getRules()) {
				stack.addAll(rule.successors(current));
			}
		}
	}
}
