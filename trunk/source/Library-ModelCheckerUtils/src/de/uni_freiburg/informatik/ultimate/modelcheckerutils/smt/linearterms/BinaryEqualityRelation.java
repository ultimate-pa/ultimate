/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Objects of this class represent binary equals relations (i.e. terms of the
 * form (= a b)) and their negations (i.e. terms of the form
 * (not (= a b)) resp. (distinct a b)).
 * @author Matthias Heizmann
 *
 */
public class BinaryEqualityRelation extends BinaryRelation {

	public BinaryEqualityRelation(Term term)
			throws NoRelationOfThisKindException {
		super(term);
	}

	@Override
	protected void checkSort(Term[] params)
			throws NoRelationOfThisKindException {
		// do nothing, every Sort is ok
	}

	@Override
	protected RelationSymbol getRelationSymbol(String functionSymbolName,
			boolean isNegated) throws NoRelationOfThisKindException {
		RelationSymbol symb = null;
		if (functionSymbolName.equals("=")) {
			symb = RelationSymbol.valueOf("EQ");
		} else if (functionSymbolName.equals("distinct")) {
			symb = RelationSymbol.valueOf("DISTINCT");
		} else {
			throw new NoRelationOfThisKindException(
					"no equality relation symbol");
		}
		symb = isNegated ? negateRelation(symb) : symb;
		return symb;
	}

}
