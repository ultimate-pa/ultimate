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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.ETransitionType;

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

	public final static int NO_PRIORITY = -1;
	/**
	 * Provides a fast access to the Duplicator auxiliary vertices that
	 * represent the choice of Duplicator after Spoiler has made a decision.
	 * Those vertices are connected to the destinations and represent the exit
	 * of a summary path.
	 */
	private final Map<STATE, DuplicatorNwaVertex<LETTER, STATE>> mChoiceToDuplicatorAux;
	/**
	 * Provides a fast access to the Spoiler auxiliary vertices that represent
	 * the choice of Duplicator after Spoiler has made a decision. Those
	 * vertices also hold the priority of the summary path.
	 */
	private final Map<STATE, SpoilerNwaVertex<LETTER, STATE>> mChoiceToSpoilerAux;
	/**
	 * Destinations of the edge, accessible by their Duplicator choices.
	 */
	private final Map<STATE, SpoilerNwaVertex<LETTER, STATE>> mDestinations;

	/**
	 * The Duplicator auxiliary vertex that represents the choice of Spoiler. It
	 * is the entry of the summarize edge
	 */
	private final DuplicatorNwaVertex<LETTER, STATE> mDuplicatorAux;
	/**
	 * Choices Duplicator can take, where the key of the map is Spoilers choice.
	 */
	private final Set<STATE> mDuplicatorChoices;
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
	 * {@link #NO_PRIORITY} and can be set via the provided methods.
	 * 
	 * @param src
	 *            Source of the edge
	 * @param spoilerChoice
	 *            The choice Spoiler did take for this summarize edge
	 * @param duplicatorChoices
	 *            Choices Duplicator can take, where the key of the map is
	 *            Spoilers choice.
	 * @param graphGeneration
	 *            The game graph generation object to add the edge to
	 */
	public SummarizeEdge(final SpoilerNwaVertex<LETTER, STATE> src, final STATE spoilerChoice,
			final Set<STATE> duplicatorChoices, final NwaGameGraphGeneration<LETTER, STATE> graphGeneration) {
		mGraphGeneration = graphGeneration;
		mSrc = src;
		mSpoilerChoice = spoilerChoice;
		mDuplicatorChoices = duplicatorChoices;
		mDuplicatorAux = new DuplicatorNwaVertex<LETTER, STATE>(NwaGameGraphGeneration.DUPLICATOR_PRIORITY, false, null,
				null, null, ETransitionType.SUMMARIZE_ENTRY, this);

		mDestinations = new HashMap<>();
		mChoiceToSpoilerAux = new HashMap<>();
		mChoiceToDuplicatorAux = new HashMap<>();

		initInternalMaps();
		addToGameGraph();
	}

	/**
	 * Gets the destination of the given sub-summarize edge.
	 * 
	 * @param duplicatorChoice
	 *            The choice duplicator did make, determines the sub-summarize
	 *            edge
	 * @return Returns the destination of the given sub-summarize edge
	 */
	public SpoilerNwaVertex<LETTER, STATE> getDestination(final STATE duplicatorChoice) {
		return mDestinations.get(duplicatorChoice);
	}

	/**
	 * Gets the destinations of the edge.
	 * 
	 * @return The destinations of the edge
	 */
	public Collection<SpoilerNwaVertex<LETTER, STATE>> getDestinations() {
		return mDestinations.values();
	}

	/**
	 * Gets all choices that Duplicator can make in this summarize edge.
	 * Identifies all sub-summarize edges.
	 * 
	 * @return All choices that Duplicator can make in this summarize edge.
	 *         Identifies all sub-summarize edges.
	 */
	public Set<STATE> getDuplicatorChoices() {
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
	public int getPriority(final STATE duplicatorChoice) {
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
	 * Sets the priorities of all sub-summarize edges.
	 * 
	 * @param priority
	 *            Priority to set
	 */
	public void setAllPriorities(final int priority) {
		for (SpoilerNwaVertex<LETTER, STATE> spoilerAux : mChoiceToSpoilerAux.values()) {
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
	public void setPriority(final STATE duplicatorChoice, final int priority) {
		mChoiceToSpoilerAux.get(duplicatorChoice).setPriority(priority);
	}

	/**
	 * Adds the summarize edge to the game graph.
	 */
	private void addToGameGraph() {
		// Add entry vertices
		mGraphGeneration.addDuplicatorVertex(mDuplicatorAux);
		// Connect it to the source
		mGraphGeneration.addEdge(mSrc, mDuplicatorAux);

		for (STATE choice : mDuplicatorChoices) {
			SpoilerNwaVertex<LETTER, STATE> spoilerAux = mChoiceToSpoilerAux.get(choice);
			DuplicatorNwaVertex<LETTER, STATE> duplicatorAux = mChoiceToDuplicatorAux.get(choice);

			// Add auxiliary vertices
			mGraphGeneration.addSpoilerVertex(spoilerAux);
			mGraphGeneration.addDuplicatorVertex(duplicatorAux);

			// Add edges between them
			mGraphGeneration.addEdge(mDuplicatorAux, spoilerAux);
			mGraphGeneration.addEdge(spoilerAux, duplicatorAux);

			// Connect them to the destinations
			mGraphGeneration.addEdge(duplicatorAux, mDestinations.get(choice));
		}
	}

	/**
	 * Initializes the internal maps.
	 */
	private void initInternalMaps() {
		for (STATE choice : mDuplicatorChoices) {
			SpoilerNwaVertex<LETTER, STATE> spoilerAux = new SpoilerNwaVertex<LETTER, STATE>(NO_PRIORITY, false, null,
					null, this);
			mChoiceToSpoilerAux.put(choice, spoilerAux);

			DuplicatorNwaVertex<LETTER, STATE> duplicatorAux = new DuplicatorNwaVertex<LETTER, STATE>(
					NwaGameGraphGeneration.DUPLICATOR_PRIORITY, false, null, null, null, ETransitionType.SUMMARIZE_EXIT,
					this);
			mChoiceToDuplicatorAux.put(choice, duplicatorAux);

			SpoilerVertex<LETTER, STATE> dest = mGraphGeneration.getSpoilerVertex(mSpoilerChoice, choice, false, null,
					null);
			if (dest instanceof SpoilerNwaVertex<?, ?>) {
				mDestinations.put(choice, (SpoilerNwaVertex<LETTER, STATE>) dest);
			}
		}
	}
}
