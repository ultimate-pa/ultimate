package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;

/**
 * This {@link IResultReporter} does not generate any results.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class SilentReporter<ACTION> implements IResultReporter<ACTION> {

	@Override
	public void reportPossibleError(ACTION start, ACTION end) {

	}

	@Override
	public void reportSafe(ACTION elem) {

	}

	@Override
	public void reportSafe(ACTION elem, String msg) {

	}
}