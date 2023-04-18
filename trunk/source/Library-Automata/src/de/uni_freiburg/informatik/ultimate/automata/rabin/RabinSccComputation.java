package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;

public class RabinSccComputation<NODE> extends DefaultSccComputation<NODE> {

	public RabinSccComputation(final ILogger logger, final ISuccessorProvider<NODE> successorProvider,
			final int numberOfAllNodes, final Set<NODE> startNodes) {
		super(logger, successorProvider, numberOfAllNodes, startNodes);
		mBalls.removeIf(x -> !x.getNodes().contains(startNodes));
	}

}
