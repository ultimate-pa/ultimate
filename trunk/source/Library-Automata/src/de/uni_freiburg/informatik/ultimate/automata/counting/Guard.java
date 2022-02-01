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

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;

/**
 * Data structure for the guards of Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */

public class Guard {

	private Counter mCounterLeft;
	private Counter mCounterRight;
	private Integer mConstant;
	private RelationSymbol mRelationSymbol;
	private TermType mTermType;
	
	public Guard()
	{}
	
	public Guard(Counter c1, Counter c2, Integer constant, RelationSymbol relation, TermType term) {
		mCounterLeft = c1;
		mCounterRight = c2;
		mConstant = constant;
		mRelationSymbol = relation;
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
	
	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}
	
	public TermType getTermType() {
		return mTermType;
	}
	
	public void changeConstant(Integer newConstant) {
		mConstant = newConstant;
	}
	
	public void changeRelationType(RelationSymbol newRelationSymbol) {
		mRelationSymbol = newRelationSymbol;
	}
	
	public void changeTermType(TermType newTermType) {
		mTermType = newTermType;
	}
	
	public Guard copyGuard() {
		Counter copyC1 = null;
		Counter copyC2 = null;
		if (mCounterLeft != null) {
			copyC1 = mCounterLeft.copyCounter();
		}
		if (mCounterRight != null) {
			copyC2 = mCounterLeft.copyCounter();
		}
		Guard copy = new Guard(copyC1, copyC2, mConstant, mRelationSymbol, mTermType);
		return copy;
	}
}
