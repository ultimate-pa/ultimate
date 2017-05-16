package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;

public class ParrotInteractiveIterationInfo {
	private RefinementStrategy mFallbackStrategy;
	// private int mNextInteractiveIteration;

	/*
	 * public ParrotInteractiveIterationInfo(final RefinementStrategy fallbackTrack, final int nextInteractiveIteration)
	 * { setData(fallbackTrack, nextInteractiveIteration); }
	 */

	public ParrotInteractiveIterationInfo(final RefinementStrategy fallbackStrategy) {
		setFallbackStrategy(fallbackStrategy);
	}

	public synchronized RefinementStrategy getFallbackStrategy() {
		return mFallbackStrategy;
	}

	public void setFrom(final ParrotInteractiveIterationInfo other) {
		// setData(other.getFallbackStrategy(), other.getNextInteractiveIteration());
		setFallbackStrategy(other.getFallbackStrategy());
	}

	public synchronized void setFallbackStrategy(final RefinementStrategy fallbackStrategy) {
		mFallbackStrategy = fallbackStrategy;
	}

	/*
	 * public int getNextInteractiveIteration() { return mNextInteractiveIteration; }
	 * 
	 * private void setData(final RefinementStrategy fallbackTrack, final int nextInteractiveIteration) {
	 * mFallbackStrategy = fallbackTrack; mNextInteractiveIteration = nextInteractiveIteration; }
	 * 
	 * public void setNextInteractiveIteration(final int iteration) { mNextInteractiveIteration = iteration; }
	 */
}
