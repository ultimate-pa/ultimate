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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PetriNetAutomatonAST extends AutomatonAST {

	/**
	 * 
	 */
	private static final long serialVersionUID = -3606354736361896683L;
	private List<String> malphabet;
	private List<String> mplaces;
	
	private List<PetriNetTransitionAST> mtransitions;
	private PetriNetMarkingListAST minitialMarkings;
	private List<String> macceptingPlaces;
	
	
//alex: I commented this, because it is called nowhere and an automaton without a name causes problems
//	public PetriNetAutomatonAST(ILocation loc) { 
//		super(loc);
//		mtransitions = new ArrayList<PetriNetTransitionAST>();
//		minitialMarkings = new PetriNetMarkingListAST(loc);
//		macceptingPlaces = new ArrayList<String>();
//	}
	
	public PetriNetAutomatonAST(ILocation loc, String name) {
		super(loc, name);
//		mName = name;
	}


	public List<String> getAlphabet() {
		return malphabet;
	}

	public void setAlphabet(List<String> malphabet) {
		this.malphabet = malphabet;
	}

	public List<String> getPlaces() {
		return mplaces;
	}

	public void setPlaces(List<String> mplaces) {
		this.mplaces = mplaces;
	}

	public List<PetriNetTransitionAST> getTransitions() {
		return mtransitions;
	}

	public void setTransitions(List<PetriNetTransitionAST> mtransitions) {
		this.mtransitions = mtransitions;
	}

	public PetriNetMarkingListAST getInitialMarkings() {
		return minitialMarkings;
	}

	public void setInitialMarkings(PetriNetMarkingListAST minitialMarkings) {
		this.minitialMarkings = minitialMarkings;
	}

	public List<String> getAcceptingPlaces() {
		return macceptingPlaces;
	}

	public void setAcceptingPlaces(List<String> macceptingPlaces) {
		this.macceptingPlaces = macceptingPlaces;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("PetriNet(" + mName + ") "+ "[Size of alphabet: ");
		builder.append(malphabet.size());
		builder.append(" Num of places: ");
		builder.append(mplaces.size());
		builder.append(" Num of transitions: ");
		builder.append(mtransitions.size());
		builder.append("]");
		return builder.toString();
	}

}
