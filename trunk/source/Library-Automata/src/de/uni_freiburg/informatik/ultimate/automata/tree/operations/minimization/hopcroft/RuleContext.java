package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.hopcroft;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;

/**
 * A rule context represents several rules that are equal with respect to a
 * partition of the states. It allows the registration of specific rules source
 * tuples and provides a collective access to them.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <LETTER>
 *            The class for letters of the rules under this context
 * @param <STATE>
 *            The class for states of the rules under this context
 */
public final class RuleContext<LETTER extends IRankedLetter, STATE> {

	/**
	 * A representative of the block of states that is allowed as destination of
	 * rules under this context.
	 */
	private final STATE mDestinationRepresentative;
	/**
	 * The letter of the rules under this context.
	 */
	private final LETTER mLetter;
	/**
	 * A list representing the signature of source states of rules under this
	 * context. For every position in the source tuple it contains a representative
	 * for the block of states that is allowed at that position.
	 */
	private final List<STATE> mSourceRepresentatives;
	/**
	 * A list containing, for a fixed position, all registered source states.
	 */
	private final ArrayList<LinkedHashSet<STATE>> mSources;

	/**
	 * Creates a new rule context that represents rules that are equal to the given
	 * signature, with respect to a partition of the states.
	 * 
	 * @param sourceRepresentatives
	 *            A list of representative states for the blocks of sources of rules
	 *            under this context
	 * @param letter
	 *            The letter of rules under this context
	 * @param destinationRepresentative
	 *            A representative state for the block of destinations of rules
	 *            under this context
	 */
	public RuleContext(final List<STATE> sourceRepresentatives, final LETTER letter,
			final STATE destinationRepresentative) {
		this.mSourceRepresentatives = sourceRepresentatives;
		this.mLetter = letter;
		this.mDestinationRepresentative = destinationRepresentative;

		this.mSources = new ArrayList<>(this.mSourceRepresentatives.size());
	}

	/**
	 * Adds the given source-tuple to this context.
	 * 
	 * @param source
	 *            The source-tuple to add
	 */
	public void addSource(final List<STATE> source) {
		if (source.size() != this.mSourceRepresentatives.size()) {
			throw new IllegalArgumentException("The size of the given list must be equal to the size of this context.");
		}

		final Iterator<STATE> sourceIterator = source.iterator();
		for (int i = 0; i < source.size(); i++) {
			final STATE sourceToAdd = sourceIterator.next();

			LinkedHashSet<STATE> statesAtPosition = this.mSources.get(i);
			if (statesAtPosition == null) {
				statesAtPosition = new LinkedHashSet<>();
				this.mSources.set(i, statesAtPosition);
			}

			statesAtPosition.add(sourceToAdd);
		}
	}

	/**
	 * Gets the representative state for the block of destinations of rules under
	 * this context
	 * 
	 * @return The representative state for the block of destinations of rules under
	 *         this context
	 */
	public STATE getDestinationRepresentative() {
		return this.mDestinationRepresentative;
	}

	/**
	 * Gets the letter of rules under this context
	 * 
	 * @return The letter of rules under this context
	 */
	public LETTER getLetter() {
		return this.mLetter;
	}

	/**
	 * Gets the state that represents allowed source states for that position under
	 * this context.
	 * 
	 * @param position
	 *            The corresponding position between <tt>0</tt> (inclusive and the
	 *            <tt>length of this contexts source tuple</tt> (exclusive)
	 * @return The state that represents allowed source states for that position
	 *         under this context
	 */
	public STATE getSourceRepresentativeAtPosition(final int position) {
		if (position < 0 || position >= this.mSourceRepresentatives.size()) {
			throw new IllegalArgumentException(
					"The position must be between 0 (inclusive) and the length of this contexts source tuple (exclusive).");
		}

		return this.mSourceRepresentatives.get(position);
	}

	/**
	 * Gets a list representing the signature of source states of rules under this
	 * context. For every position in the source tuple it contains a representative
	 * for the block of states that is allowed at that position. The list is backed
	 * with the context.
	 * 
	 * @return A backed list of source representatives of this context
	 */
	public List<STATE> getSourceRepresentatives() {
		return this.mSourceRepresentatives;
	}

	/**
	 * Gets a list of registered source-tuples. The list is backed with the context.
	 * 
	 * @return A backed list of registered source-tuples
	 */
	public List<? extends Set<STATE>> getSources() {
		return this.mSources;
	}

	/**
	 * Gets the size of the source tuple.
	 * 
	 * @return The size of the source tuple
	 */
	public int getSourceSize() {
		return this.mSourceRepresentatives.size();
	}

	/**
	 * Gets all source states registered at the given position. The set is backed
	 * with the context.
	 * 
	 * @param position
	 *            The corresponding position between <tt>0</tt> (inclusive and the
	 *            <tt>length of this contexts source tuple</tt> (exclusive)
	 * @return A backed set of source states registered at the given position
	 */
	public Set<STATE> getSourceStatesAtPosition(final int position) {
		if (position < 0 || position >= this.mSources.size()) {
			throw new IllegalArgumentException(
					"The position must be between 0 (inclusive) and the length of this contexts source tuple (exclusive).");
		}

		return this.mSources.get(position);
	}
}
