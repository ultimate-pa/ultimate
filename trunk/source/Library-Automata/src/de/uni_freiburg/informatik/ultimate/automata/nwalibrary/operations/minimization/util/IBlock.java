/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.util;

import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * Interface for a general block data structure inside a partition.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public interface IBlock<STATE> {
	/**
	 * @return true iff block contains an initial state
	 */
	public boolean isInitial();
	
	/**
	 * @return true iff block contains an final state
	 */
	public boolean isFinal();
	
	/**
	 * @param stateFactory state factory
	 * @return state constructed by state factory
	 */
	public STATE minimize(final StateFactory<STATE> stateFactory);
	
	/**
	 * @return iterator over all states
	 */
	public Iterator<STATE> statesIterator();
	
	/**
	 * If a block is independent of the representative, then one must only look
	 * at one state in the block when interested in the successor blocks.
	 * 
	 * Since internal and call transitions are considered similarly by many
	 * operations, they are handled the same way.
	 * 
	 * NOTE: We assume here that return transitions are more complicated and
	 * cannot be handled independent of the representative.
	 * 
	 * @return true iff all states have the same outgoing transitions
	 */
	public boolean isRepresentativeIndependentInternalsCalls();
}
