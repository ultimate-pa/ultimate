package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;

/**
 * IDebugHelper is used to implement some assertions in the {@link FixpointEngine}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IDebugHelper<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION> {

	/**
	 * Check whether the Hoare triple {stateBeforeLeaving} {stateAfterLeaving} transition {\/ postStates} holds.
	 *
	 * @param stateBeforeLeaving
	 *            The abstract state in the old scope, i.e., the scope that we are leaving.
	 * @param stateAfterLeaving
	 *            The abstract state in the new scope, i.e., the scope that we are entering.
	 * @param postStates
	 *            All abstract post states.
	 * @param transition
	 *            The transition.
	 * @return true iff the Hoare triple holds.
	 */
	boolean isPostSound(final STATE stateBeforeLeaving, final STATE stateAfterLeaving, final List<STATE> postStates,
			final ACTION transition);

	boolean isPostSound(final AbstractMultiState<STATE, ACTION, VARDECL> stateBeforeLeaving,
			final AbstractMultiState<STATE, ACTION, VARDECL> stateAfterLeaving,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState, final ACTION transition);
}
