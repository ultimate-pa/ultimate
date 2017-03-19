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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ContainsSubterm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;


/**
 * A given term, an equal term and the index at which this equality occurred.
 * @author Matthias Heizmann
 */
public class EqualityInformation {

	private final int mIndex;
	private final Term mGivenTerm;
	private final Term mEqualTerm;

	public EqualityInformation(int index, Term givenTerm, Term equalTerm) {
		mIndex = index;
		mGivenTerm = givenTerm;
		mEqualTerm = equalTerm;
	}

	public int getIndex() {
		return mIndex;
	}

	public Term getVariable() {
		return mGivenTerm;
	}

	public Term getTerm() {
		return mEqualTerm;
	}
	
	
	/**
	 * Check all terms in context if they are an equality of the form givenTerm
	 * == t, such that t does not contain the subterm forbiddenTerm. If this is
	 * the case return corresponding equality information, otherwise return
	 * null. If forbiddenTerm is null all subterms in t are allowed.
	 */
	public static EqualityInformation getEqinfo(Script script, Term givenTerm, Term[] context, Term forbiddenTerm,
			int quantifier) {
		final BinaryEqualityRelation[] binaryRelations = new BinaryEqualityRelation[context.length];

		// stage 1: check if there is an "=" or "distinct" term where the
		// givenTerm is on one hand side of the relation.
		for (int i = 0; i < context.length; i++) {
			if (!isSubterm(givenTerm, context[i])) {
				continue;
			}
			try {
				binaryRelations[i] = new BinaryEqualityRelation(context[i]);
			} catch (final NoRelationOfThisKindException e2) {
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

			final Term lhs = binaryRelations[i].getLhs();
			final Term rhs = binaryRelations[i].getRhs();

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
					affRel = new AffineRelation(script, context[i]);
				} catch (final NotAffineException e1) {
					continue;
				}
				if (affRel.isVariable(givenTerm)) {
					Term equalTerm;
					try {
						final ApplicationTerm equality = affRel.onLeftHandSideOnly(script, givenTerm);
						equalTerm = equality.getParameters()[1];
					} catch (final NotAffineException e) {
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
