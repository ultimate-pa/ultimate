package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class LoggingHelper {

	private LoggingHelper() {
		// this is a util class
	}

	public static <STATE extends IAbstractState<STATE, ?, ?>> StringBuilder getStateString(final STATE current) {
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
}
