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

/**
 * Data structure for the updates of Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */

public class Update {

	private Counter mCounterLeft;
	private Counter mCounterRight;
	private Integer mConstant;
	private TermType mTermType;
	
	public Update()
	{}
	
	public Update(Counter c1, Counter c2, Integer constant, TermType term) {
		mCounterLeft = c1;
		mCounterRight = c2;
		mConstant = constant;
		mTermType = term;
	}

	public Counter getCounterLeft() {
		return mCounterLeft;
	}
	
	public Counter getCounterRight() {
		return mCounterRight;
	}
	
	public Integer getConstant() {
		return mConstant;
	}
	
	public TermType getTermType() {
		return mTermType;
	}
	
	public Update copyUpdate() {
		Update copy = new Update(mCounterLeft.copyCounter(), mCounterRight.copyCounter(), mConstant, mTermType);
		return copy;
	}
}
