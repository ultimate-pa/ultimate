/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.models.ILocation;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PetriNetAutomatonAST extends AutomatonAST {

	/**
	 * 
	 */
	private static final long serialVersionUID = -3606354736361896683L;
	private List<String> m_alphabet;
	private List<String> m_places;
	
	private List<PetriNetTransitionAST> m_transitions;
	private PetriNetMarkingListAST m_initialMarkings;
	private List<String> m_acceptingPlaces;
	
	
	public PetriNetAutomatonAST(ILocation loc) {
		super(loc);
		m_transitions = new ArrayList<PetriNetTransitionAST>();
		m_initialMarkings = new PetriNetMarkingListAST(loc);
		m_acceptingPlaces = new ArrayList<String>();
	}
	
	public PetriNetAutomatonAST(ILocation loc, String name) {
		super(loc);
		m_Name = name;
	}


	public List<String> getAlphabet() {
		return m_alphabet;
	}

	public void setAlphabet(List<String> m_alphabet) {
		this.m_alphabet = m_alphabet;
	}

	public List<String> getPlaces() {
		return m_places;
	}

	public void setPlaces(List<String> m_places) {
		this.m_places = m_places;
	}

	public List<PetriNetTransitionAST> getTransitions() {
		return m_transitions;
	}

	public void setTransitions(List<PetriNetTransitionAST> m_transitions) {
		this.m_transitions = m_transitions;
	}

	public PetriNetMarkingListAST getInitialMarkings() {
		return m_initialMarkings;
	}

	public void setInitialMarkings(PetriNetMarkingListAST m_initialMarkings) {
		this.m_initialMarkings = m_initialMarkings;
	}

	public List<String> getAcceptingPlaces() {
		return m_acceptingPlaces;
	}

	public void setAcceptingPlaces(List<String> m_acceptingPlaces) {
		this.m_acceptingPlaces = m_acceptingPlaces;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("PetriNet(" + m_Name + ") "+ "[Size of alphabet: ");
		builder.append(m_alphabet.size());
		builder.append(" Num of places: ");
		builder.append(m_places.size());
		builder.append(" Num of transitions: ");
		builder.append(m_transitions.size());
		builder.append("]");
		return builder.toString();
	}

}
