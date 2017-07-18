package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;

/**
 * {@link IDebugHelper} is used to implement some assertions in the {@link FixpointEngine}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IDebugHelper<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL, LOCATION> {

	/**
	 * Check whether the Hoare triple {preState} {hierachicalPreState} transition {postState} holds.
	 *
	 * Note that {@link AbstractMultiState} is a disjunction of abstract states.
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
	boolean isPostSound(final AbstractMultiState<STATE, VARDECL> preState,
			final AbstractMultiState<STATE, VARDECL> hierachicalPreState,
			final AbstractMultiState<STATE, VARDECL> postState, final ACTION transition);
}
