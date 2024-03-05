package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

public class Configuration<S> {
	private final ImmutableList<S> mStates;

	public Configuration(final ImmutableList<S> states) {
		mStates = states;
	}

	public boolean contains(final S predecessor) {
		return mStates.contains(predecessor);
	}

	public int size() {
		return mStates.size();
	}

	public S get(final int i) {
		return mStates.get(i);
	}

	public Configuration<S> replace(final int i, final S successor) {
		final var list = IntStream.range(0, mStates.size()).mapToObj(j -> j == i ? successor : get(j))
				.collect(Collectors.toList());
		return new Configuration<>(new ImmutableList<>(list));
	}

	public Configuration<S> replace(final Map<Integer, S> subst) {
		final var list = IntStream.range(0, mStates.size()).mapToObj(j -> subst.getOrDefault(j, get(j)))
				.collect(Collectors.toList());
		return new Configuration<>(new ImmutableList<>(list));
	}

	@Override
	public int hashCode() {
		return Objects.hash(mStates);
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
		final Configuration other = (Configuration) obj;
		return Objects.equals(mStates, other.mStates);
	}

	@Override
	public String toString() {
		return mStates.toString();
	}
}
