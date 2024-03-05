package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.List;
import java.util.function.Consumer;

public class Explorer<S> {
	private final Program<S> mProgram;
	private final List<Configuration<S>> mInitialConfigurations;

	public Explorer(final Program<S> program, final List<Configuration<S>> initialConfigurations) {
		mProgram = program;
		mInitialConfigurations = initialConfigurations;
	}

	public void dfs(final Consumer<Configuration<S>> consumer) {
		final var stack = new ArrayDeque<Configuration<S>>();
		final var visited = new HashSet<Configuration<S>>();
		stack.addAll(mInitialConfigurations);

		while (!stack.isEmpty()) {
			final var current = stack.pop();
			if (!visited.add(current)) {
				continue;
			}
			consumer.accept(current);

			for (final var rule : mProgram.getRules()) {
				if (rule.isApplicable(current)) {
					stack.addAll(rule.successors(current));
				}
			}
		}
	}
}
