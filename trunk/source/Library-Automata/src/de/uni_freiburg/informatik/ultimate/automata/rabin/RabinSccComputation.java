package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Removes all Sccs which do not have a loop back to their beginning
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <NODE>
 *            The node type Sccs are constructed on
 */
public class RabinSccComputation<NODE> extends DefaultSccComputation<NODE> {

	public RabinSccComputation(final ILogger logger, final ISuccessorProvider<NODE> successorProvider,
			final int numberOfAllNodes, final Set<NODE> startNodes) {
		super(logger, successorProvider, numberOfAllNodes, startNodes);

		final HashSet<StronglyConnectedComponent<NODE>> temp = new HashSet<>();
		for (int i = 0; i < mBalls.size(); i++) {
			for (final NODE node : startNodes) {
				if (mBalls.get(i).getNodes().contains(node)) {
					temp.add(mBalls.get(i));
				}
			}
		}

		mBalls.retainAll(temp);
	}

}
