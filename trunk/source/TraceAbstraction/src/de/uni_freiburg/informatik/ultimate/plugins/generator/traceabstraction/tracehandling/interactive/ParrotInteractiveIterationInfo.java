package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.MultiTrackTraceAbstractionRefinementStrategy.Track;

public class ParrotInteractiveIterationInfo {
	private Track mFallbackTrack;
	private int mNextInteractiveIteration;

	public ParrotInteractiveIterationInfo(final Track fallbackTrack, final int nextInteractiveIteration) {
		setData(fallbackTrack, nextInteractiveIteration);
	}

	public ParrotInteractiveIterationInfo() {
	}

	public Track getFallbackTrack() {
		return mFallbackTrack;
	}

	public int getNextInteractiveIteration() {
		return mNextInteractiveIteration;
	}

	private void setData(final Track fallbackTrack, final int nextInteractiveIteration) {
		mFallbackTrack = fallbackTrack;
		mNextInteractiveIteration = nextInteractiveIteration;
	}

	public void setFrom(ParrotInteractiveIterationInfo other) {
		setData(other.getFallbackTrack(), other.getNextInteractiveIteration());
	}
}
