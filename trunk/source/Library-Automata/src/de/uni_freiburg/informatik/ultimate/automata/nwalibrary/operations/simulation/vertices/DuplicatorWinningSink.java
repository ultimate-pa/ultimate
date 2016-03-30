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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices;

/**
 * Represents a sink that is winning for Duplicator. If such a sink exists with
 * <tt>sinkEntry</tt> it means that one can move from that vertex into a sink
 * with priority 0, which is winning for Duplicator. In detail such a sink is
 * <b>sinkEntry -> DuplicatorSink -> SpoilerSink -> DuplicatorSink -> ...</b>.
 * Where <tt>SpoilerSink</tt> has a priority of 0.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class DuplicatorWinningSink<LETTER, STATE> {

	/**
	 * The duplicator vertex of this sink.
	 */
	private final DuplicatorDoubleDeckerVertex<LETTER, STATE> m_DuplicatorSink;
	/**
	 * The entry vertex of this sink.
	 */
	private final SpoilerDoubleDeckerVertex<LETTER, STATE> m_SinkEntry;
	/**
	 * The spoiler vertex of this sink.
	 */
	private final SpoilerDoubleDeckerVertex<LETTER, STATE> m_SpoilerSink;

	/**
	 * Creates a new sink which starts at <tt>sinkEntry</tt>.
	 * 
	 * @param sinkEntry
	 *            The vertex where the sink starts
	 */
	public DuplicatorWinningSink(final SpoilerDoubleDeckerVertex<LETTER, STATE> sinkEntry) {
		m_SinkEntry = sinkEntry;
		m_DuplicatorSink = new DuplicatorDoubleDeckerVertex<LETTER, STATE>(2, false, null, null, null,
				TransitionType.SINK, this);
		m_SpoilerSink = new SpoilerDoubleDeckerVertex<LETTER, STATE>(0, false, null, null, this);
	}

	/**
	 * Gets the duplicator vertex of this sink.
	 * 
	 * @return The entry vertex of this sink.
	 */
	public DuplicatorDoubleDeckerVertex<LETTER, STATE> getDuplicatorSink() {
		return m_DuplicatorSink;
	}

	/**
	 * Gets the entry vertex of this sink.
	 * 
	 * @return The entry vertex of this sink.
	 */
	public SpoilerDoubleDeckerVertex<LETTER, STATE> getSinkEntry() {
		return m_SinkEntry;
	}

	/**
	 * Gets the spoiler vertex of this sink.
	 * 
	 * @return The entry vertex of this sink.
	 */
	public SpoilerDoubleDeckerVertex<LETTER, STATE> getSpoilerSink() {
		return m_SpoilerSink;
	}

}
