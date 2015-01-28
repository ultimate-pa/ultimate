package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ContainsSubterm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;


/**
 * A given term, an equal term and the index at which this equality occurred.
 * @author Matthias Heizmann
 */
public class EqualityInformation {

	private final int m_Index;
	private final Term m_GivenTerm;
	private final Term m_EqualTerm;

	public EqualityInformation(int index, Term givenTerm, Term equalTerm) {
		m_Index = index;
		m_GivenTerm = givenTerm;
		m_EqualTerm = equalTerm;
	}

	public int getIndex() {
		return m_Index;
	}

	public Term getVariable() {
		return m_GivenTerm;
	}

	public Term getTerm() {
		return m_EqualTerm;
	}
	
	
	/**
	 * Check all terms in context if they are an equality of the form givenTerm
	 * == t, such that t does not contain the subterm forbiddenTerm. If this is
	 * the case return corresponding equality information, otherwise return
	 * null. If forbiddenTerm is null all subterms in t are allowed.
	 * 
	 * @param logger
	 */
	public static EqualityInformation getEqinfo(Script script, Term givenTerm, Term[] context, Term forbiddenTerm,
			int quantifier, Logger logger) {
		BinaryEqualityRelation[] binaryRelations = new BinaryEqualityRelation[context.length];

		// stage 1: check if there is an "=" or "distinct" term where the
		// givenTerm is on one hand side of the relation.
		for (int i = 0; i < context.length; i++) {
			if (!isSubterm(givenTerm, context[i])) {
				continue;
			}
			try {
				binaryRelations[i] = new BinaryEqualityRelation(context[i]);
			} catch (NoRelationOfThisKindException e2) {
				continue;
			}

			if (binaryRelations[i].getRelationSymbol().toString().equals("=") && quantifier == QuantifiedFormula.FORALL) {
				binaryRelations[i] = null;
				continue;
			} else if (binaryRelations[i].getRelationSymbol().toString().equals("distinct")
					&& quantifier == QuantifiedFormula.EXISTS) {
				binaryRelations[i] = null;
				continue;
			}

			Term lhs = binaryRelations[i].getLhs();
			Term rhs = binaryRelations[i].getRhs();

			if (lhs.equals(givenTerm) && !isSubterm(givenTerm, rhs)) {
				if (forbiddenTerm == null || !isSubterm(forbiddenTerm, rhs)) {
					return new EqualityInformation(i, givenTerm, rhs);
				}
			}
			if (rhs.equals(givenTerm) && !isSubterm(givenTerm, lhs)) {
				if (forbiddenTerm == null || !isSubterm(forbiddenTerm, lhs)) {
					return new EqualityInformation(i, givenTerm, lhs);
				}
			}
		}
		// stage 2: also rewrite linear terms if necessary to get givenTerm
		// to one hand side of the binary relation.
		for (int i = 0; i < context.length; i++) {
			if (binaryRelations[i] == null) {
				// not even binary equality relation that contains givenTerm
				continue;
			} else {
				AffineRelation affRel;
				try {
					affRel = new AffineRelation(context[i]);
				} catch (NotAffineException e1) {
					continue;
				}
				if (affRel.isVariable(givenTerm)) {
					Term equalTerm;
					try {
						ApplicationTerm equality = affRel.onLeftHandSideOnly(script, givenTerm);
						equalTerm = equality.getParameters()[1];
					} catch (NotAffineException e) {
						// no representation where var is on lhs
						continue;
					}
					if (isSubterm(givenTerm, equalTerm)) {
						// this case occurs e.g. if the given term also occurs
						// in some select term
						continue;
					}
					if (forbiddenTerm != null && isSubterm(forbiddenTerm, equalTerm)) {
						continue;
					} else {
						return new EqualityInformation(i, givenTerm, equalTerm);
					}
				}
			}
		}
		// no equality information found
		return null;
	}
	
	
	/**
	 * Returns true if subterm is a subterm of term.
	 */
	private static boolean isSubterm(Term subterm, Term term) {
		return (new ContainsSubterm(subterm)).containsSubterm(term);
	}

}
