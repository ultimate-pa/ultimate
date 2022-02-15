package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.util.statistics.MeasureDefinition;
import de.uni_freiburg.informatik.ultimate.util.statistics.PrettyPrint;

public class SizeIterationPair {

	public static final MeasureDefinition KEY_TYPE = new MeasureDefinition(() -> new SizeIterationPair(-1, -1),
			SizeIterationPair::aggregate, PrettyPrint::keyColonData, a -> ((SizeIterationPair) a).isEmpty());

	final int mSize;
	final int mIteration;

	public SizeIterationPair() {
		this(-1, -1);
	}

	public SizeIterationPair(final int size, final int iteration) {
		mSize = size;
		mIteration = iteration;
	}

	public int getSize() {
		return mSize;
	}

	public int getIteration() {
		return mIteration;
	}

	@Override
	public String toString() {
		return "size=" + mSize + "occurred in iteration=" + mIteration;
	}

	public boolean isEmpty() {
		return mSize == -1 && mIteration == -1;
	}

	public static SizeIterationPair aggregate(final Object a, final Object b) {
		final SizeIterationPair aSip = (SizeIterationPair) a;
		final SizeIterationPair bSip = (SizeIterationPair) b;
		return aSip.getSize() >= bSip.getSize() ? aSip : bSip;
	}

}