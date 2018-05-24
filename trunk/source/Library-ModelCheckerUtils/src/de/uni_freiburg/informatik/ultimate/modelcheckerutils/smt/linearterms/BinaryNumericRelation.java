/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;

/**
 * Represents a relation of the form ψ ▷ φ, where the terms ψ and φ have 
 * numeric sort and ▷ is one of the following relation symbols
 * {=, <=, >=, <, >, !=, distinct }.
 * This class is only a helper that can be used to detect if a relation has this
 * form.
 *
 * @author Matthias Heizmann
 */
public class BinaryNumericRelation extends BinaryRelation {

	public BinaryNumericRelation(Term term) throws NoRelationOfThisKindException {
		super(term);
	}
	
	protected BinaryNumericRelation(RelationSymbol relationSymbol, Term lhs, Term rhs) {
		super(relationSymbol, lhs, rhs);
	}


	@Override
	protected void checkSort(Term[] params)
			throws NoRelationOfThisKindException {
		if (!params[0].getSort().isNumericSort() && 
				!SmtSortUtils.isBitvecSort(params[0].getSort())) {
			throw new NoRelationOfThisKindException("not numeric");
		} else {
			assert params[1].getSort().isNumericSort() || 
				SmtSortUtils.isBitvecSort(params[1].getSort());
		}
	}

	@Override
	protected RelationSymbol getRelationSymbol(String functionSymbolName,
			boolean isNegated) throws NoRelationOfThisKindException {
		RelationSymbol relSymb = null;
		for (final RelationSymbol symb : RelationSymbol.values()) {
			if (symb.toString().equals(functionSymbolName)) {
				relSymb = isNegated ? negateRelation(symb) : symb;
				break;
			}
		}
		if (relSymb == null) {
			throw new NoRelationOfThisKindException(
					"no binary numberic relation symbol");
		} else {
			return relSymb;
		}
	}

	/**
	 * Returns a new BinaryNumericRelation that has the RelationSymbol relSymb
	 * and the same lhs and rhs as this BinaryNumericRelation.
	 */
	public BinaryNumericRelation changeRelationSymbol(RelationSymbol relSymb) {
		return new BinaryNumericRelation(relSymb, getLhs(), getRhs());
	}


	

}
