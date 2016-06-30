package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph.NwaGameGraphGeneration;

/**
 * Implementation of a StateFactory for game automaton used for summarize edge
 * computation in NWA game graphs. A game automaton uses SpoilerVertex as states
 * and GameLetter as letters.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class GameAutomatonFactory<LETTER, STATE> extends StateFactory<SpoilerVertex<LETTER, STATE>> {

	/**
	 * The state that represents an empty stack.
	 */
	private SpoilerVertex<LETTER, STATE> emptyStackState;
	/**
	 * State factory used by the NWA automaton.
	 */
	private StateFactory<STATE> mStateFactoryOfNwa;

	/**
	 * Creates a new instance of a game automaton factory object.
	 * 
	 * @param stateFactoryOfNwa
	 *            State factory used by the NWA automaton.
	 */
	public GameAutomatonFactory(StateFactory<STATE> stateFactoryOfNwa) {
		mStateFactoryOfNwa = stateFactoryOfNwa;
		STATE emptyStackStateOfNwa = mStateFactoryOfNwa.createEmptyStackState();
		emptyStackState = new SpoilerVertex<LETTER, STATE>(NwaGameGraphGeneration.DUPLICATOR_PRIORITY, false,
				emptyStackStateOfNwa, emptyStackStateOfNwa);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory#
	 * createEmptyStackState()
	 */
	@Override
	public SpoilerVertex<LETTER, STATE> createEmptyStackState() {
		return emptyStackState;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory#
	 * determinize(java.util.Map)
	 */
	@Override
	public SpoilerVertex<LETTER, STATE> determinize(
			Map<SpoilerVertex<LETTER, STATE>, Set<SpoilerVertex<LETTER, STATE>>> down2up) {
		return null;
	}
}