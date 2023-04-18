package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

public class RabinSccComputation<NODE> extends DefaultSccComputation<NODE> {

	public RabinSccComputation(final ILogger logger, final ISuccessorProvider<NODE> successorProvider,
			final int numberOfAllNodes, final Set<NODE> startNodes) {
		super(logger, successorProvider, numberOfAllNodes, startNodes);

		final boolean[] acceptingBalls = new boolean[mBalls.size()];

		for (int i = 0; i < mBalls.size(); i++) {
			for (final NODE node : startNodes) {
				if (mBalls.get(i).getNodes().contains(node)) {
					acceptingBalls[i] = true;
				}
			}
		}

		final ArrayList<StronglyConnectedComponent<NODE>> temp = new ArrayList<>();
		for (int i = 0; i < acceptingBalls.length; i++) {
			if (acceptingBalls[i]) {
				temp.add(mBalls.get(i));
			}

		}
		mBalls.clear();
		mBalls.addAll(temp);
	}

}
