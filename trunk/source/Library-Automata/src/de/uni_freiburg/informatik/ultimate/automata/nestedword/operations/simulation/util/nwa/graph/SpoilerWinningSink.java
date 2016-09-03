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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.ETransitionType;

/**
 * Represents a sink that is winning for Spoiler. If such a sink exists with
 * <tt>sinkEntry</tt> it means that one can move from that vertex into a sink
 * with priority 1, which is winning for Spoiler. In detail such a sink is
 * <b>sinkEntry -> SpoilerSink -> DuplicatorSink -> SpoilerSink -> ...</b>.
 * Where <tt>SpoilerSink</tt> has a priority of 1.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SpoilerWinningSink<LETTER, STATE> implements IWinningSink<LETTER, STATE> {

	/**
	 * The priority that is winning for Spoiler.
	 */
	private static final int SPOILER_WINNING_PRIORITY = 1;

	/**
	 * The duplicator vertex of this sink.
	 */
	private final DuplicatorNwaVertex<LETTER, STATE> mDuplicatorSink;

	/**
	 * The game graph this sink belongs to.
	 */
	private final AGameGraph<LETTER, STATE> mGraph;

	/**
	 * The spoiler vertex of this sink.
	 */
	private final SpoilerNwaVertex<LETTER, STATE> mSpoilerSink;

	/**
	 * Creates a new sink that initially is not connected to the game graph.
	 * Therefore {@link #addToGraph()} must be used. Multiple entries can be
	 * added using {@link #connectToEntry(DuplicatorNwaVertex)}.
	 * 
	 * @param graph
	 *            The game graph this sink belongs to
	 */
	public SpoilerWinningSink(final AGameGraph<LETTER, STATE> graph) {
		mGraph = graph;
		mSpoilerSink = new SpoilerNwaVertex<LETTER, STATE>(SPOILER_WINNING_PRIORITY, false, null, null, this);
		mDuplicatorSink = new DuplicatorNwaVertex<LETTER, STATE>(NwaGameGraphGeneration.DUPLICATOR_PRIORITY, false,
				null, null, null, ETransitionType.SINK, this);
	}

	/**
	 * Adds this sink to the game graph.
	 */
	public void addToGraph() {
		// Add auxiliary vertices
		mGraph.addSpoilerVertex(mSpoilerSink);
		mGraph.addDuplicatorVertex(mDuplicatorSink);

		// Add edges
		mGraph.addEdge(mSpoilerSink, mDuplicatorSink);
		mGraph.addEdge(mDuplicatorSink, mSpoilerSink);
	}

	/**
	 * Connects the given vertex to this sink.
	 * 
	 * @param sinkEntry
	 *            Sink entry to connect
	 */
	public void connectToEntry(final DuplicatorNwaVertex<LETTER, STATE> sinkEntry) {
		mGraph.addEdge(sinkEntry, mSpoilerSink);
	}

	/**
	 * Gets the duplicator vertex of this sink.
	 * 
	 * @return The entry vertex of this sink.
	 */
	public DuplicatorNwaVertex<LETTER, STATE> getDuplicatorAuxiliarySink() {
		return mDuplicatorSink;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.util.nwa.IWinningSink#getPriority()
	 */
	@Override
	public int getPriority() {
		return SPOILER_WINNING_PRIORITY;
	}

	/**
	 * Gets the spoiler vertex of this sink.
	 * 
	 * @return The entry vertex of this sink.
	 */
	public SpoilerNwaVertex<LETTER, STATE> getSpoilerAuxiliarySink() {
		return mSpoilerSink;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.
	 * simulation.util.nwa.graph.IWinningSink#isWinningForSpoiler()
	 */
	@Override
	public boolean isWinningForSpoiler() {
		return true;
	}
}
