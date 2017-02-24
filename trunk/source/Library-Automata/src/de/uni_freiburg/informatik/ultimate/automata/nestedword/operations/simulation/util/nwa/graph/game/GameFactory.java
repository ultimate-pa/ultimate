package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 * Implementation of a StateFactory for game automaton used for summarize edge
 * computation in NWA game graphs. A game automaton uses IGameState, which
 * usually are Spoiler vertices, as states and GameLetter as letters.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class GameFactory implements ISinkStateFactory<IGameState>, IDeterminizeStateFactory<IGameState>,
		IEmptyStackStateFactory<IGameState> {
	/**
	 * The state that represents an empty stack.
	 */
	private final IGameState mEmptyStackState;
	/**
	 * The state that represents an empty stack.
	 */
	private final IGameState mSinkState;

	/**
	 * Creates a new instance of a game automaton factory object.
	 */
	public GameFactory() {
		mEmptyStackState = new GameEmptyState();
		mSinkState = new GameSinkState();
	}

	@Override
	public IGameState createEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public IGameState createSinkStateContent() {
		return mSinkState;
	}

	@Override
	public IGameState determinize(final Map<IGameState, Set<IGameState>> down2up) {
		return new GameDoubleDeckerSet(down2up);
	}
}
