/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.states;


/**
 * Represents a state which can be exactly one of two given states.<br>
 * State of this kind are used in the 
 * {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#union union algorithm} 
 * to realize the disjoint union of the state sets of the two supplied finite tree automata.<br>
 * <br>
 * <em>For any object of this class, the following conditions are true:</em>
 * <ul>
 * <li> isFirstKind() != isSecondKind() </li>
 * <li> isFirstKind() == true implies asFirstKind() != null </li>
 * <li> isSecondKind() == true implies asSecondKind() != null </li>
 * </ul>
 * 
 * @param <Q1> type of the first given state
 * @param <Q2> type of the second given state
 * 
 * @author Dorothea, Irene, Martin
 */
public interface BiState<Q1 extends State, Q2 extends State> extends State {

	/**
	 * Returns whether this state represents the first state given in the constructor.
	 * @return true if the first state given was not null, false otherwise
	 */
	public boolean isFirstKind();


	/**
	 * Returns whether this state represents the second state given in the constructor.
	 * @return true if the second state given was not null, false otherwise
	 */
	public boolean isSecondKind();


	/**
	 * Returns the first state given in the constructor.
	 * @return the first state given in the constructor
	 */
	public Q1 asFirstKind();


	/**
	 * Returns the second state given in the constructor.
	 * @return the second state given in the constructor
	 */
	public Q2 asSecondKind();

}
