package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.AbstractCounterexample;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;

/**
 * This {@link IResultReporter} does not generate any results.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class SilentReporter<STATE extends IAbstractState<STATE>, ACTION, LOCATION>
		implements IResultReporter<STATE, ACTION, LOCATION> {

	@Override
	public void
			reportPossibleError(final AbstractCounterexample<DisjunctiveAbstractState<STATE>, ACTION, LOCATION> cex) {
		// do nothing to stay silent
	}

	@Override
	public void reportFinished() {
		// do nothing to stay silent
	}
}