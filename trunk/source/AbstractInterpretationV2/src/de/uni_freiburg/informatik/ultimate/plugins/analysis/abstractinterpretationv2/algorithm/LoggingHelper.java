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

	static <STATE extends IAbstractState<STATE, ?, ?>> StringBuilder getStateString(final STATE current) {
		return addHashCodeString(new StringBuilder(), current).append(' ').append(current.toLogString());
	}

	static <ACTION> StringBuilder getTransitionString(final ACTION current,
			ITransitionProvider<ACTION, ?> transProvider) {
		return addHashCodeString(new StringBuilder(), current).append(' ').append(transProvider.toLogString(current));
	}

	static StringBuilder getHashCodeString(final Object current) {
		return addHashCodeString(new StringBuilder(), current);
	}

	static StringBuilder addHashCodeString(final StringBuilder builder, final Object current) {
		if (current == null) {
			return builder.append("[?]");
		}
		return builder.append('[').append(current.hashCode()).append(']');
	}
}
