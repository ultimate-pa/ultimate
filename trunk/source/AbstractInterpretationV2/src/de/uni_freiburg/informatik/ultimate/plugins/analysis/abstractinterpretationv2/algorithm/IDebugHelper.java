package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;

/**
 * {@link IDebugHelper} is used to implement some assertions in the {@link FixpointEngine}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IDebugHelper<STATE extends IAbstractState<STATE>, ACTION, VARDECL, LOCATION> {

	/**
	 * Check whether the Hoare triple {preState} {hierachicalPreState} transition {postState} holds.
	 *
	 * Note that {@link DisjunctiveAbstractState} is a disjunction of abstract states.
	 *
	 * @param preState
	 *            The abstract pre state in the current scope.
	 * @param hierachicalPreState
	 *            The abstract state from which we were called.
	 * @param postStates
	 *            The abstract post state.
	 * @param transition
	 *            The transition.
	 * @return true iff the Hoare triple holds.
	 */
	boolean isPostSound(final DisjunctiveAbstractState<STATE> preState,
			final DisjunctiveAbstractState<STATE> hierachicalPreState,
			final DisjunctiveAbstractState<STATE> postState, final ACTION transition);
}
