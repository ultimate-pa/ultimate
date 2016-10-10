package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers;

/**
 * A list element that knows it's own position in the minimizer's input sequence.
 */
public interface HasSequenceIndex {
	int getSequenceIndex();
}
