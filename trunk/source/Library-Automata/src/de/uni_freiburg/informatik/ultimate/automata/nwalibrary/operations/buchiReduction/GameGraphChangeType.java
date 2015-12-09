package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

/**
 * Types of possible game graph changes.
 * 
 * @author Daniel Tischner
 *
 */
public enum GameGraphChangeType {
	/**
	 * Represents a change that did not alter the game graph.
	 */
	NO_CHANGE,
	/**
	 * Represents a change that added something to the game graph.
	 */
	ADDITION,
	/**
	 * Represents a change that removed something from the game graph.
	 */
	REMOVAL
}
