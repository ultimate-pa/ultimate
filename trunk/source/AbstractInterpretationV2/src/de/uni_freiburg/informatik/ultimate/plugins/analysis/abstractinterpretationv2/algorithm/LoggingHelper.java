package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class LoggingHelper {

	private LoggingHelper() {
		// this is a util class
	}

	public static <STATE extends IAbstractState<STATE>> StringBuilder getStateString(final STATE current) {
		if (current == null) {
			return new StringBuilder("__");
		}
		return addHashCodeString(new StringBuilder(), current).append(' ').append(current.toLogString());
	}

	public static <ACTION> StringBuilder getTransitionString(final ACTION current,
			final ITransitionProvider<ACTION, ?> transProvider) {
		return addHashCodeString(new StringBuilder(), current).append(' ').append(transProvider.toLogString(current));
	}

	public static StringBuilder getHashCodeString(final Object current) {
		return addHashCodeString(new StringBuilder(), current);
	}

	public static StringBuilder addHashCodeString(final StringBuilder builder, final Object current) {
		if (current == null) {
			return builder.append("[?]");
		}
		return builder.append('[').append(current.hashCode()).append(']');
	}

	public static <ACTION, STORE extends IAbstractStateStorage<?, ACTION, ?>> String
			getScopeStackString(final Deque<Pair<ACTION, STORE>> scopeStack) {
		return scopeStack.stream().sequential().map(a -> a.getFirst())
				.map(a -> a == null ? "[G]" : getHashCodeString(a).toString()).reduce((a, b) -> a + b)
				.orElseThrow(AssertionError::new);
	}

	public static String getPrecedessorSequence(final WorklistItem<?, ?, ?, ?> item) {
		if (item == null) {
			return "???";
		}
		final StringBuilder sb = new StringBuilder();
		WorklistItem<?, ?, ?, ?> currentItem = item;
		while (currentItem.getPredecessor() != null) {
			sb.append(currentItem.toExtendedString()).append(CoreUtil.getPlatformLineSeparator());
			currentItem = currentItem.getPredecessor();
		}
		return sb.toString();
	}
}
