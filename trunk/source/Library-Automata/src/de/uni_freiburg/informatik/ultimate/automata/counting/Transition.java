/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.counting;

import java.util.ArrayList;

/**
 * Data structure for the transitions of Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */

public class Transition<LETTER, STATE> {
	
	private LETTER mLetter;
	private STATE mPredecessorState;
	private STATE mSuccessorState;
	private ArrayList<ArrayList<Guard>> mGuards;
	private ArrayList<Update> mUpdates;
	
	public Transition()
	{}
	
	public Transition(LETTER letter,
			STATE preS,
			STATE sucS,
			ArrayList<ArrayList<Guard>> guards,
			ArrayList<Update> updates){
		mLetter = letter;
		mPredecessorState = preS;
		mSuccessorState = sucS;
		mGuards = guards;
		mUpdates = updates;
	}

	public LETTER getLetter() {
		return mLetter;
	}
	
	public STATE getPreState() {
		return mPredecessorState;
	}
	
	public STATE getSucState() {
		return mSuccessorState;
	}
	
	public ArrayList<ArrayList<Guard>> getGuards() {
		return mGuards;
	}
	
	public ArrayList<Update> getUpdates() {
		return mUpdates;
	}
	
	public Transition<LETTER, STATE> copyTransition() {
		ArrayList<ArrayList<Guard>> guardDNFCopy = new ArrayList<ArrayList<Guard>>();
		for (ArrayList<Guard> list : mGuards) {
			ArrayList<Guard> guardListCopy = new ArrayList<Guard>();
			for (Guard guard : list) {
				Guard guardCopy = guard.copyGuard();
				guardListCopy.add(guardCopy);
			}
			guardDNFCopy.add(guardListCopy);
		}
		
		ArrayList<Update> updateListCopy = new ArrayList<Update>();
		for (Update update : mUpdates) {
			Update updateCopy = update.copyUpdate();
			updateListCopy.add(updateCopy);
		}
		
		Transition<LETTER, STATE> copy = new Transition<LETTER, STATE>(mLetter, mPredecessorState, mSuccessorState, guardDNFCopy, updateListCopy);
		return copy;
	}
}
