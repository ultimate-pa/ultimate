/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;


public class PetriNetNot1SafeException extends AutomataLibraryException {

	private static final long serialVersionUID = -8776962353437660445L;

	private static final String MESSAGE = "Petri net not 1-safe";

	private final Collection<?> mUnsafePlaces;

	public PetriNetNot1SafeException(final Class<?> thrower) {
		super(thrower, MESSAGE);
		mUnsafePlaces = null;
	}

	public PetriNetNot1SafeException(final Class<?> thrower, final Collection<?> unsafePlaces) {
		super(thrower, MESSAGE);
		mUnsafePlaces = unsafePlaces;
	}

	@Override
	public String getMessage() {
		if (mUnsafePlaces == null) {
			return super.getMessage();
		} else {
			return super.getMessage() + " The following places may contain more than one token."
					+ mUnsafePlaces.toString();
		}
	}

	public Collection<?> getUnsafePlaces() {
		return mUnsafePlaces;
	}




}
