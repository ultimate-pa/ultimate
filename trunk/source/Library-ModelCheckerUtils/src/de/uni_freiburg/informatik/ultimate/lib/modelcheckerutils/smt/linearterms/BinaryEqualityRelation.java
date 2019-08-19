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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Objects of this class represent binary equals relations (i.e. terms of the
 * form (= a b)) and their negations (i.e. terms of the form
 * (not (= a b)) resp. (distinct a b)).
 * @author Matthias Heizmann
 *
 */
public class BinaryEqualityRelation extends BinaryRelation {

	public BinaryEqualityRelation(final Term term)
			throws NoRelationOfThisKindException {
		super(term);
	}

	private BinaryEqualityRelation(final RelationSymbol relSymb, final Term lhs, final Term rhs) {
		super(relSymb, lhs, rhs);
	}

	@Override
	protected void checkSort(final Term[] params)
			throws NoRelationOfThisKindException {
		// do nothing, every Sort is ok
	}

	@Override
	protected RelationSymbol getRelationSymbol(final String functionSymbolName,
			final boolean isNegated) throws NoRelationOfThisKindException {
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


	public static BinaryEqualityRelation convert(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return null;
		}
		ApplicationTerm appTerm = (ApplicationTerm) term;
		String functionSymbolName = appTerm.getFunction().getName();
		Term[] params = appTerm.getParameters();
		boolean isNegated;
		if (functionSymbolName.equals("not")) {
			assert params.length == 1;
			final Term notTerm = params[0];
			if (!(notTerm instanceof ApplicationTerm)) {
				return null;
			}
			isNegated = true;
			appTerm = (ApplicationTerm) notTerm;
			functionSymbolName = appTerm.getFunction().getName();
			params = appTerm.getParameters();
		} else {
			isNegated = false;
		}
		if (appTerm.getParameters().length != 2) {
			return null;
		}
		if (!appTerm.getFunction().isIntern()) {
			return null;
		}
		RelationSymbol relSymb = RelationSymbol.convert(functionSymbolName);
		if (relSymb == null) {
			return null;
		}
		if (relSymb != RelationSymbol.EQ && relSymb != RelationSymbol.DISTINCT) {
			return null;
		}
		if (isNegated) {
			relSymb = BinaryRelation.negateRelation(relSymb);
		}
		return new BinaryEqualityRelation(relSymb, params[0], params[1]);
	}

}
