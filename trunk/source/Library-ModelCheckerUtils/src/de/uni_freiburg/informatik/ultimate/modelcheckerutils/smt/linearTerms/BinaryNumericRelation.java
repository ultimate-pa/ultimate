package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import de.uni_freiburg.informatik.ultimate.logic.Term;

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
		if (!params[0].getSort().isNumericSort()) {
			throw new NoRelationOfThisKindException("not numeric");
		} else {
			assert params[1].getSort().isNumericSort();
		}
	}

	@Override
	protected RelationSymbol getRelationSymbol(String functionSymbolName,
			boolean isNegated) throws NoRelationOfThisKindException {
		RelationSymbol relSymb = null;
		for (RelationSymbol symb : RelationSymbol.values()) {
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
