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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ContainsSubterm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class that stores information about an equality or disequality
 * of a given term.
 *
 * @author Matthias Heizmann
 */
public class EqualityInformation {

	private final int mIndex;
	private final Term mGivenTerm;
	private final Term mEqualTerm;
	private final RelationSymbol mRelationSymbol;

	public EqualityInformation(final int index, final Term givenTerm, final Term equalTerm,
			final RelationSymbol relationSymbol) {
		mIndex = index;
		mGivenTerm = givenTerm;
		mEqualTerm = equalTerm;
		mRelationSymbol = relationSymbol;
	}

	@Deprecated
	public int getIndex() {
		return mIndex;
	}

	/**
	 * @return Term for which the information is provided.
	 */
	public Term getGivenTerm() {
		return mGivenTerm;
	}

	/**
	 *
	 * @return Term that is in relation (equality/disequality) to the given term.
	 */
	public Term getRelatedTerm() {
		return mEqualTerm;
	}

	/**
	 *
	 * @return Kind of realation between given term and related term.
	 */
	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}


	/**
	 * Check all terms in the <code>context</code> if they are an equality of the
	 * form <code>givenTerm == t</code> (resp. disequality of the form
	 * <code>givenTerm == t</code>, such that t does not contain the subterm
	 * <code>forbiddenTerm</code>. If this is the case return corresponding equality
	 * information, otherwise return null. If forbiddenTerm is null all subterms in
	 * t are allowed. If <code>quantifier</code> is the existential quantifier, we
	 * check for equalities otherwise (universal quantifier) we check for
	 * disequalities.
	 */
	public static EqualityInformation getEqinfo(final Script script, final Term givenTerm, final Term[] context,
			final Term forbiddenTerm, final int quantifier) {
		final BinaryEqualityRelation[] binaryRelations = new BinaryEqualityRelation[context.length];

		// stage 1: check if there is an "=" or "distinct" term where the
		// givenTerm is on one hand side of the relation.
		for (int i = 0; i < context.length; i++) {
			if (!isSubterm(givenTerm, context[i])) {
				continue;
			}
			binaryRelations[i] = BinaryEqualityRelation.convert(context[i]);
			if (binaryRelations[i] == null) {
				continue;
			}

			if (binaryRelations[i].getRelationSymbol().equals(RelationSymbol.EQ)
					&& quantifier == QuantifiedFormula.FORALL) {
				binaryRelations[i] = null;
				continue;
			} else if (binaryRelations[i].getRelationSymbol().equals(RelationSymbol.DISTINCT)
					&& quantifier == QuantifiedFormula.EXISTS) {
				binaryRelations[i] = null;
				continue;
			}

			final BinaryEqualityRelation ber = binaryRelations[i];
			final EqualityInformation eqInfo = getEqinfo(givenTerm, ber, forbiddenTerm, i);
			final SolvedBinaryRelation sbr = ber.solveForSubject(script, givenTerm);
			assert (sbr == null) == (eqInfo == null) : "sbr: " + sbr + " eqInfo: " + eqInfo;
			if (eqInfo != null) {
				return eqInfo;
			}
		}
		// stage 2: also rewrite linear terms if necessary to get givenTerm
		// to one hand side of the binary relation.
		for (int i = 0; i < context.length; i++) {
			if (binaryRelations[i] == null) {
				// not even binary equality relation that contains givenTerm
				continue;
			}
			final AffineRelation affRel = AffineRelation.convert(script, context[i]);
			if (affRel == null) {
				continue;
			}
			final EqualityInformation eqInfo = getEqinfo(script, givenTerm, affRel, forbiddenTerm, i);
			if (eqInfo != null) {
				return eqInfo;
			}
		}
		// no equality information found
		return null;
	}

	public static EqualityInformation getEqinfo(final Script script, final Term givenTerm, final AffineRelation affRel,
			final Term forbiddenTerm, final int i) {
		if (affRel.isVariable(givenTerm)) {
			Term equalTerm;
			final SolvedBinaryRelation sbr = affRel.solveForSubject(script, givenTerm);
			if (sbr == null || !sbr.getAssumptionsMap().isEmpty()) {
				return null;
			} else {
				equalTerm = sbr.getRightHandSide();
			}
			if (forbiddenTerm != null && isSubterm(forbiddenTerm, equalTerm)) {
				return null;
			}
			return new EqualityInformation(i, givenTerm, equalTerm, affRel.getRelationSymbol());
		}
		return null;
	}

	public static EqualityInformation getEqinfo(final Term givenTerm, final BinaryEqualityRelation ber,
			final Term forbiddenTerm, final int i) {
		final Term lhs = ber.getLhs();
		final Term rhs = ber.getRhs();

		if (lhs.equals(givenTerm) && !isSubterm(givenTerm, rhs)) {
			if (forbiddenTerm == null || !isSubterm(forbiddenTerm, rhs)) {
				return new EqualityInformation(i, givenTerm, rhs, ber.getRelationSymbol());
			}
		}
		if (rhs.equals(givenTerm) && !isSubterm(givenTerm, lhs)) {
			if (forbiddenTerm == null || !isSubterm(forbiddenTerm, lhs)) {
				return new EqualityInformation(i, givenTerm, lhs, ber.getRelationSymbol());
			}
		}
		return null;
	}

	public static Pair<Set<Term>, Set<Term>> getEqTerms(final Script script, final Term givenTerm, final Term[] context,
			final Term forbiddenTerm) {
		final Set<Term> equivalentTerms = new HashSet<>();
		final Set<Term> disjointTerms = new HashSet<>();
		for (int i = 0; i < context.length; i++) {
			final AffineRelation affRel = AffineRelation.convert(script, context[i]);
			if (affRel == null) {
				continue;
			}
			final EqualityInformation eqInfo = getEqinfo(script, givenTerm, affRel, forbiddenTerm, i);
			if (eqInfo != null) {
				switch (eqInfo.getRelationSymbol()) {
				case DISTINCT:
					disjointTerms.add(eqInfo.getRelatedTerm());
					break;
				case EQ:
					equivalentTerms.add(eqInfo.getRelatedTerm());
					break;
				case GEQ:
				case GREATER:
				case LEQ:
				case LESS:
					// do nothing
					break;
				default:
					throw new AssertionError();
				}
			}
		}
		return new Pair<>(equivalentTerms, disjointTerms);

	}

	/**
	 * Returns true if subterm is a subterm of term.
	 */
	private static boolean isSubterm(final Term subterm, final Term term) {
		return (new ContainsSubterm(subterm)).containsSubterm(term);
	}

}
