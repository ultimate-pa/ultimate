package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;

/**
 * IDebugHelper is used to implement some assertions in the {@link FixpointEngine}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IDebugHelper<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL, LOCATION> {
	
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
	default boolean isPostSound(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final Set<STATE> postStates, final ACTION transition) {
		return isPostSound(Collections.singleton(stateBeforeLeaving), Collections.singleton(stateBeforeLeaving),
				postStates, transition);
	}

	boolean isPostSound(final AbstractMultiState<STATE, ACTION, VARDECL> stateBeforeLeaving,
			final AbstractMultiState<STATE, ACTION, VARDECL> stateAfterLeaving,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState, final ACTION transition);

	boolean isPostSound(final Set<STATE> statesBeforeLeaving, final Set<STATE> stateAfterLeaving,
			final Set<STATE> postStates, final ACTION transition);
}
