/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa;

/**
 * Worklist which saves pairs of generic entries (W, I) where W is called <i>work</i> I is called <i>input</i>.
 * The order in which items are inserted into the queue is up to each class implementing this interface.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <W> Type of the work entries
 * @param <I> Type of the input entries
 */
public interface IWorklistWithInputs<W, I> {

	/**
	 * Adds or updates an entry.
	 * If {@code work} is already queued, its old and new input are merged and its position is kept.
	 * If {@code work} is new to this queue, adds it to the tail.
	 *
	 * @param work Work entry
	 * @param addInput Input for work entry
	 */
	void add(W work, I addInput);

	/**
	 * If this queue contains entries, removes the next entry.
	 * The removed entry can be queried with {@link #getWork()} and {@link #getInput()}.
	 * <p>
	 * Calling advance on an empty worklist has no effect.
	 *
	 * @return The queue contained at least one entry, the next entry was removed.
	 */
	boolean advance();

	/**
	 * @see #advance()
	 */
	W getWork();

	/**
	 * @see #advance()
	 */
	I getInput();

}
