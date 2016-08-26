/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.ETransitionType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Summarize edge that summarizes transitions representing moves on the same
 * stack level. If a summarize edge from <tt>src</tt> to <tt>dest</tt> exists it
 * means that one can move from that vertex to the vertex ending up with the
 * same stack level than before. Such edges connect Spoiler vertices with
 * Spoiler vertices. To ensure a a legal game graph it creates auxiliary
 * vertices between the source and destination. A summarize edge contains
 * sub-summarize edges that offer Duplicator the possibility to make a decision
 * between several paths. Each sub-summarize edge can be assigned a priority. By
 * default the priorities are not valid and need to be assigned after creation,
 * else the graph is in an illegal state.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SummarizeEdge<LETTER, STATE> {

	public static final int NO_PRIORITY = -1;
	/**
	 * Destinations of the edge, accessible by their Duplicator choices.
	 */
	private final Map<Pair<STATE, Boolean>, SpoilerNwaVertex<LETTER, STATE>> mChoiceToDestination;
	/**
	 * Provides a fast access to the Duplicator auxiliary vertices that
	 * represent the choice of Duplicator after Spoiler has made a decision.
	 * Those vertices are connected to the destinations and represent the exit
	 * of a summary path.
	 */
	private final Map<Pair<STATE, Boolean>, DuplicatorNwaVertex<LETTER, STATE>> mChoiceToDuplicatorAux;
	/**
	 * Provides a fast access to the Spoiler auxiliary vertices that represent
	 * the choice of Duplicator after Spoiler has made a decision. Those
	 * vertices also hold the priority of the summary path.
	 */
	private final Map<Pair<STATE, Boolean>, SpoilerNwaVertex<LETTER, STATE>> mChoiceToSpoilerAux;
	/**
	 * Spoiler invoker of the edge, accessible by their Duplicator choices.
	 */
	private final Map<Pair<STATE, Boolean>, Set<SpoilerNwaVertex<LETTER, STATE>>> mChoiceToSpoilerInvokers;

	/**
	 * The Duplicator auxiliary vertex that represents the choice of Spoiler. It
	 * is the entry of the summarize edge
	 */
	private final DuplicatorNwaVertex<LETTER, STATE> mDuplicatorAux;
	/**
	 * Choices Duplicator can take with the bit it leads to.
	 */
	private final Set<Pair<STATE, Boolean>> mDuplicatorChoices;
	/**
	 * The game graph generation object this edge belongs to.
	 */
	private final NwaGameGraphGeneration<LETTER, STATE> mGraphGeneration;
	/**
	 * The choice Spoiler did make for this summarize edge, used as identifier.
	 */
	private final STATE mSpoilerChoice;
	/**
	 * Source of the edge.
	 */
	private final SpoilerNwaVertex<LETTER, STATE> mSrc;

	/**
	 * Creates a new summarize edge with given source and destination vertices.
	 * The priorities of the sub-summaries are initially all
	 * {@link #NO_PRIORITY} and can be set via the provided methods. The
	 * summarize edge initially is not connected to the game graph,
	 * {@link #addToGameGraph()} must be used.
	 * 
	 * @param src
	 *            Source of the edge
	 * @param spoilerChoice
	 *            The choice Spoiler did take for this summarize edge
	 * @param duplicatorChoices
	 *            Choices Duplicator can take with the bit it leads to
	 * @param graphGeneration
	 *            The game graph generation object to add the edge to
	 */
	public SummarizeEdge(final SpoilerNwaVertex<LETTER, STATE> src, final STATE spoilerChoice,
			final Set<Pair<STATE, Boolean>> duplicatorChoices,
			final NwaGameGraphGeneration<LETTER, STATE> graphGeneration) {
		// TODO This object can not handle Sink-targets because Duplicator and
		// Spoiler choices then are null. Evaluate if this should be fixed or
		// not.
		mGraphGeneration = graphGeneration;
		mSrc = src;
		mSpoilerChoice = spoilerChoice;
		mDuplicatorChoices = duplicatorChoices;
		mDuplicatorAux = new DuplicatorNwaVertex<LETTER, STATE>(NwaGameGraphGeneration.DUPLICATOR_PRIORITY, false,
				spoilerChoice, null, null, ETransitionType.SUMMARIZE_ENTRY, this);

		mChoiceToDestination = new HashMap<>();
		mChoiceToSpoilerAux = new HashMap<>();
		mChoiceToDuplicatorAux = new HashMap<>();
		mChoiceToSpoilerInvokers = new HashMap<>();

		initInternalMaps();
	}

	/**
	 * Adds the summarize edge to the game graph.
	 */
	public void addToGameGraph() {
		// Add entry vertices
		mGraphGeneration.addDuplicatorVertex(mDuplicatorAux);
		// Connect it to the source
		mGraphGeneration.addEdge(mSrc, mDuplicatorAux);

		for (final Pair<STATE, Boolean> choiceEntry : mDuplicatorChoices) {
			final SpoilerNwaVertex<LETTER, STATE> spoilerAux = mChoiceToSpoilerAux.get(choiceEntry);
			final DuplicatorNwaVertex<LETTER, STATE> duplicatorAux = mChoiceToDuplicatorAux.get(choiceEntry);

			// Add auxiliary vertices
			mGraphGeneration.addSpoilerVertex(spoilerAux);
			mGraphGeneration.addDuplicatorVertex(duplicatorAux);

			// Add edges between them
			mGraphGeneration.addEdge(mDuplicatorAux, spoilerAux);
			mGraphGeneration.addEdge(spoilerAux, duplicatorAux);

			// Connect them to the destinations
			mGraphGeneration.addEdge(duplicatorAux, mChoiceToDestination.get(choiceEntry));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof SummarizeEdge)) {
			return false;
		}
		final SummarizeEdge<?, ?> other = (SummarizeEdge<?, ?>) obj;
		if (mDuplicatorChoices == null) {
			if (other.mDuplicatorChoices != null) {
				return false;
			}
		} else if (!mDuplicatorChoices.equals(other.mDuplicatorChoices)) {
			return false;
		}
		if (mSpoilerChoice == null) {
			if (other.mSpoilerChoice != null) {
				return false;
			}
		} else if (!mSpoilerChoice.equals(other.mSpoilerChoice)) {
			return false;
		}
		if (mSrc == null) {
			if (other.mSrc != null) {
				return false;
			}
		} else if (!mSrc.equals(other.mSrc)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the destination of the given sub-summarize edge.
	 * 
	 * @param duplicatorChoice
	 *            The choice duplicator did make, determines the sub-summarize
	 *            edge
	 * @return Returns the destination of the given sub-summarize edge
	 */
	public SpoilerNwaVertex<LETTER, STATE> getDestination(final Pair<STATE, Boolean> duplicatorChoice) {
		return mChoiceToDestination.get(duplicatorChoice);
	}

	/**
	 * Gets the destinations of the edge.
	 * 
	 * @return The destinations of the edge
	 */
	public Collection<SpoilerNwaVertex<LETTER, STATE>> getDestinations() {
		return mChoiceToDestination.values();
	}

	/**
	 * Gets all choices that Duplicator can make in this summarize edge.
	 * Identifies all sub-summarize edges.
	 * 
	 * @return All choices that Duplicator can make in this summarize edge.
	 *         Identifies all sub-summarize edges.
	 */
	public Set<Pair<STATE, Boolean>> getDuplicatorChoices() {
		return mDuplicatorChoices;
	}

	/**
	 * Gets the priority of the given sub-summarize edge.
	 * 
	 * @param duplicatorChoice
	 *            The choice duplicator did make, determines the sub-summarize
	 *            edge
	 * @return Returns the priority of the given sub-summarize edge
	 */
	public int getPriority(final Pair<STATE, Boolean> duplicatorChoice) {
		return mChoiceToSpoilerAux.get(duplicatorChoice).getPriority();
	}

	/**
	 * Gets the source of the edge.
	 * 
	 * @return The source of the edge
	 */
	public SpoilerVertex<LETTER, STATE> getSource() {
		return mSrc;
	}

	/**
	 * Gets the choice Spoiler did take for this summarize edge
	 * 
	 * @return The choice Spoiler did take for this summarize edge
	 */
	public STATE getSpoilerChoice() {
		return mSpoilerChoice;
	}

	/**
	 * Gets the spoiler invokers of the given sub-summarize edge.
	 * 
	 * @param duplicatorChoice
	 *            The choice duplicator did make, determines the sub-summarize
	 *            edge
	 * @return Returns the spoiler invokers of the given sub-summarize edge
	 */
	public Set<SpoilerNwaVertex<LETTER, STATE>> getSpoilerInvokers(final Pair<STATE, Boolean> duplicatorChoice) {
		return mChoiceToSpoilerInvokers.get(duplicatorChoice);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDuplicatorChoices == null) ? 0 : mDuplicatorChoices.hashCode());
		result = prime * result + ((mSpoilerChoice == null) ? 0 : mSpoilerChoice.hashCode());
		result = prime * result + ((mSrc == null) ? 0 : mSrc.hashCode());
		return result;
	}

	/**
	 * Sets the priorities of all sub-summarize edges.
	 * 
	 * @param priority
	 *            Priority to set
	 */
	public void setAllPriorities(final int priority) {
		for (final SpoilerNwaVertex<LETTER, STATE> spoilerAux : mChoiceToSpoilerAux.values()) {
			spoilerAux.setPriority(priority);
		}
	}

	/**
	 * Sets the priority of the given sub-summarize edge.
	 * 
	 * @param duplicatorChoice
	 *            The choice duplicator did make, determines the sub-summarize
	 *            edge
	 * @param priority
	 *            The priority to set
	 */
	public void setPriority(final Pair<STATE, Boolean> duplicatorChoice, final int priority) {
		mChoiceToSpoilerAux.get(duplicatorChoice).setPriority(priority);
	}

	/**
	 * Initializes the internal maps.
	 */
	private void initInternalMaps() {
		for (final Pair<STATE, Boolean> choiceEntry : mDuplicatorChoices) {
			final STATE choice = choiceEntry.getFirst();
			final boolean choiceBit = choiceEntry.getSecond();

			// Spoiler auxiliary that holds the priority
			final SpoilerNwaVertex<LETTER, STATE> spoilerAux = new SpoilerNwaVertex<LETTER, STATE>(NO_PRIORITY,
					choiceBit, null, choice, this);
			mChoiceToSpoilerAux.put(choiceEntry, spoilerAux);

			// Duplicator auxiliary that is the end
			final DuplicatorNwaVertex<LETTER, STATE> duplicatorAux = new DuplicatorNwaVertex<LETTER, STATE>(
					NwaGameGraphGeneration.DUPLICATOR_PRIORITY, choiceBit, null, choice, null,
					ETransitionType.SUMMARIZE_EXIT, this);
			mChoiceToDuplicatorAux.put(choiceEntry, duplicatorAux);

			// Destination
			final SpoilerVertex<LETTER, STATE> dest = mGraphGeneration.getSpoilerVertex(mSpoilerChoice, choice,
					choiceBit, null, null);
			if (dest instanceof SpoilerNwaVertex<?, ?>) {
				mChoiceToDestination.put(choiceEntry, (SpoilerNwaVertex<LETTER, STATE>) dest);
			}

			// Spoiler invoker
			final AGameGraph<LETTER, STATE> graph = mGraphGeneration.getGameGraph();
			for (final Vertex<LETTER, STATE> pred : graph.getPredecessors(dest)) {
				if (!(pred instanceof DuplicatorNwaVertex<?, ?>)) {
					throw new IllegalStateException(
							"Expected cast to be possible, something seems to be wrong with the game graph.");
				}
				final DuplicatorNwaVertex<LETTER, STATE> predAsDuplicatorNwa = (DuplicatorNwaVertex<LETTER, STATE>) pred;
				// We are only interested in return-predecessor
				if (!predAsDuplicatorNwa.getTransitionType().equals(ETransitionType.RETURN)) {
					continue;
				}
				// We do not consider return-predecessor that have no
				// predecessor
				final Set<Vertex<LETTER, STATE>> possibleSpoilerInvokers = graph.getPredecessors(predAsDuplicatorNwa);
				if (possibleSpoilerInvokers == null) {
					continue;
				}
				for (final Vertex<LETTER, STATE> possibleSpoilerInvoker : possibleSpoilerInvokers) {
					if (!(possibleSpoilerInvoker instanceof SpoilerNwaVertex<?, ?>)) {
						throw new IllegalStateException(
								"Expected cast to be possible, something seems to be wrong with the game graph.");
					}
					final SpoilerNwaVertex<LETTER, STATE> spoilerInvokerAsSpoilerNwa = (SpoilerNwaVertex<LETTER, STATE>) possibleSpoilerInvoker;

					// Add the invoker to the list
					Set<SpoilerNwaVertex<LETTER, STATE>> spoilerInvokers = mChoiceToSpoilerInvokers.get(choiceEntry);
					if (spoilerInvokers == null) {
						spoilerInvokers = new HashSet<>();
					}
					spoilerInvokers.add(spoilerInvokerAsSpoilerNwa);
					mChoiceToSpoilerInvokers.put(choiceEntry, spoilerInvokers);
				}
			}
		}
	}
}
