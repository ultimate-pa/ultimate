package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms;

import de.uni_freiburg.informatik.ultimate.logic.Term;

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
		symb = isNegated ? getNegation(symb) : symb;
		return symb;
	}

}
