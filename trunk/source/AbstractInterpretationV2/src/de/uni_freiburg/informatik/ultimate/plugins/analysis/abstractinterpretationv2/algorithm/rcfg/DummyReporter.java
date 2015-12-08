package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class DummyReporter<ACTION> implements IResultReporter<ACTION> {

	@Override
	public void reportPossibleError(ACTION start, ACTION end) {

	}

	@Override
	public void reportSafe() {

	}

	@Override
	public void reportSafe(String msg) {
		
	}
}
