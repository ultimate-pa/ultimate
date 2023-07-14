/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 *
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * A extension of a acceptor Petri net with finite states; Intended for use ´with Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 */
public class RabinPetriNetAST extends PetriNetAutomatonAST {

	/**
	 *
	 */
	private static final long serialVersionUID = -6021451678169305249L;
	private List<String> mFinitePlaces;

	public RabinPetriNetAST(final ILocation loc, final String name) {
		super(loc, name);
	}

	public List<String> getFinitePlaces() {
		return mFinitePlaces;
	}

	public void setFinitePlaces(final List<String> finitePlaces) {
		mFinitePlaces = finitePlaces;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("RabinPetriNet(" + mName + "): " + "[#alphabet: ");
		builder.append(super.getAlphabet().size());
		builder.append(" #places: ");
		builder.append(super.getPlaces().size());
		builder.append(" #acceptingPlaces: ");
		builder.append(super.getAcceptingPlaces().size());
		builder.append(" #finitePlaces: ");
		builder.append(getFinitePlaces().size());
		builder.append(" #transitions: ");
		builder.append(super.getTransitions().size());
		builder.append("]");
		return builder.toString();
	}
}
