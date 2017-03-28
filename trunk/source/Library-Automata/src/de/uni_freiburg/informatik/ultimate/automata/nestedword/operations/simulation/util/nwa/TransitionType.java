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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa;

/**
 * Possible types of a transitions.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public enum TransitionType {
	/**
	 * Type for call transitions.
	 */
	CALL,
	/**
	 * Type for internal transitions.
	 */
	INTERNAL,
	/**
	 * Type for return transitions.
	 */
	RETURN,
	/**
	 * Type for auxiliary transitions that represent the a sink that is winning for a given player.
	 */
	SINK,
	/**
	 * Type for auxiliary transitions that represent the entry of a summarize edge.
	 */
	SUMMARIZE_ENTRY,
	/**
	 * Type for auxiliary transitions that represent the exit of a summarize edge.
	 */
	SUMMARIZE_EXIT
}
