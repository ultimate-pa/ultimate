/*
 * Copyright (C) 2009-2026 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

class AddAsAxiom implements Operation {
	/**
	 *
	 */
	private final Clausifier clausifier;
	/**
	 * The term to add as axiom. This is annotated with its proof.
	 */
	private final Term mAxiom;
	/**
	 * The source node.
	 */
	private final SourceAnnotation mSource;

	/**
	 * Add the clauses for an asserted term.
	 *
	 * @param axiom
	 *            the term to assert annotated with the proof for the corresponding unit clause.
	 * @param source
	 *            the prepared proof node containing the source annotation.
	 * @param clausifier TODO
	 */
	public AddAsAxiom(Clausifier clausifier, final Term axiom, final SourceAnnotation source) {
		this.clausifier = clausifier;
		assert axiom.getSort().getName() == "Bool";
		mAxiom = axiom;
		mSource = source;
	}

	@Override
	public void perform() {
		Term term = this.clausifier.mTracker.getProvedTerm(mAxiom);
		boolean positive = true;
		while (Clausifier.isNotTerm(term)) {
			term = Clausifier.toPositive(term);
			positive = !positive;
		}
		final int oldFlags = this.clausifier.getTermFlags(term);
		int assertedFlag, auxFlag;
		if (positive) {
			assertedFlag = Clausifier.POS_AXIOMS_ADDED;
			auxFlag = Clausifier.POS_AUX_AXIOMS_ADDED;
		} else {
			assertedFlag = Clausifier.NEG_AXIOMS_ADDED;
			auxFlag = Clausifier.NEG_AUX_AXIOMS_ADDED;
		}
		if ((oldFlags & assertedFlag) != 0) {
			// We've already added this formula as axioms
			return;
		}
		// Mark the formula as asserted.
		// Also mark the auxFlag, as it is no longer necessary to create the auxiliary axioms that state that auxlit
		// implies this formula.
		this.clausifier.setTermFlags(term, oldFlags | assertedFlag);
		final ILiteral auxlit = this.clausifier.getILiteral(term);
		if (auxlit != null) {
			// add the unit aux literal as clause; this will basically make the auxaxioms the axioms after unit
			// propagation and level 0 resolution.
			if ((oldFlags & auxFlag) == 0) {
				this.clausifier.addAuxAxioms(term, positive, mSource);
			}
			this.clausifier.buildClause(mAxiom, mSource);
			return;
		}
		final Theory t = mAxiom.getTheory();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			if (!positive && at.getFunction() == t.mOr) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// A negated or is an and of negated formulas. Hence assert all negated
				// subformulas.
				for (final Term p : at.getParameters()) {
					final Term split =
							this.clausifier.mTracker.resolveBinaryTautology(mAxiom, t.term("not", p), ProofConstants.TAUT_OR_POS);
					this.clausifier.pushOperation(new AddAsAxiom(this.clausifier, split, mSource));
				}
				return;
			} else if (positive && at.getFunction() == t.mAnd) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// Assert all subformulas of the positive and.
				for (final Term p : at.getParameters()) {
					final Term split = this.clausifier.mTracker.resolveBinaryTautology(mAxiom, p, ProofConstants.TAUT_AND_NEG);
					this.clausifier.pushOperation(new AddAsAxiom(this.clausifier, split, mSource));
				}
				return;
			} else if (!positive && at.getFunction() == t.mImplies) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// A negated implication is an and of the left-hand formulas and the negated
				// right-hand formula. This asserts these formulas.
				final Term[] params = at.getParameters();
				for (int i = 0; i < params.length; i++) {
					final Term p = i < params.length - 1 ? params[i] : t.term("not", params[i]);
					final Term split = this.clausifier.mTracker.resolveBinaryTautology(mAxiom, p, ProofConstants.TAUT_IMP_POS);
					this.clausifier.pushOperation(new AddAsAxiom(this.clausifier, split, mSource));
				}
				return;
			} else if (at.getFunction().getName().equals("xor")
					&& at.getParameters()[0].getSort() == t.getBooleanSort()) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				final Term p1 = at.getParameters()[0];
				final Term p2 = at.getParameters()[1];
				if (positive) {
					// (xor p1 p2) --> (p1 \/ p2) /\ (~p1 \/ ~p2)
					final Term pivot = t.term("not", term);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, p1, p2 },
							ProofConstants.TAUT_XOR_NEG_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource,
							new Term[] { pivot, t.term("not", p1), t.term("not", p2) },
							ProofConstants.TAUT_XOR_NEG_2);
				} else {
					// (not (xor p1 p2)) --> (p1 \/ ~p2) /\ (~p1 \/ p2)
					final Term pivot = term;
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, p1, t.term("not", p2) },
							ProofConstants.TAUT_XOR_POS_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, t.term("not", p1), p2 },
							ProofConstants.TAUT_XOR_POS_2);
				}
				return;
			} else if (at.getFunction().getName().equals("ite")) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				assert at.getFunction().getReturnSort() == t.getBooleanSort();
				final Term cond = at.getParameters()[0];
				final Term thenForm = at.getParameters()[1];
				final Term elseForm = at.getParameters()[2];
				if (positive) {
					final Term pivot = t.term("not", term);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, t.term("not", cond), thenForm },
							ProofConstants.TAUT_ITE_NEG_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, cond, elseForm },
							ProofConstants.TAUT_ITE_NEG_2);
				} else {
					final Term pivot = term;
					this.clausifier.buildClauseWithTautology(mAxiom, mSource,
							new Term[] { pivot, t.term("not", cond), t.term("not", thenForm) },
							ProofConstants.TAUT_ITE_POS_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, cond, t.term("not", elseForm) },
							ProofConstants.TAUT_ITE_POS_2);
				}
				return;
			}
		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) term;
			final Pair<Term, Annotation> convertQuantInfo = this.clausifier.convertQuantifiedSubformula(positive, qf);
			final Annotation rule = convertQuantInfo.getSecond();
			final Term skolemized = this.clausifier.mTracker.resolveBinaryTautology(mAxiom, convertQuantInfo.getFirst(), rule);
			final Term rewrite = this.clausifier.mCompiler.transform(this.clausifier.mTracker.getProvedTerm(skolemized));
			final Term newAxiom = this.clausifier.mTracker.modusPonens(skolemized, rewrite);
			this.clausifier.pushOperation(new AddAsAxiom(this.clausifier, newAxiom, mSource));
			return;
		}
		this.clausifier.buildClause(mAxiom, mSource);
	}
}