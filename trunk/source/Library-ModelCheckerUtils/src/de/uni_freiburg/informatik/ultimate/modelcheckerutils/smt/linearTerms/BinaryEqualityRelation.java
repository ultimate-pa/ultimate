package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

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
