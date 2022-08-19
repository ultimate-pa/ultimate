/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory.InstanceOrigin;

/**
 * Annotation for ground instances of quantified clauses.
 * <p>
 * The actual instantiation lemma is of the form {@code (not quantclause \/ instance}. When converting the
 * QuantAnnotation to a proof term, the resolution between the instantiation lemma and the quantified clause, seen as a
 * unit literal, is built.
 *
 * The instantiation lemma is annotated with the ground substitution for the variables that produced the instance
 * (ordered according to the order of the quantified variables in the clause), the origin of the instance (checkpoint or
 * finalcheck), and, if full proofs are produced, a proof for the equality between the substituted clause term and the
 * resulting simplified instance clause.
 *
 * The proof for the unit (quantified) clause is its clause proof as usual.
 *
 * @author Tanja Schindler
 *
 */
public class QuantAnnotation implements IAnnotation {

	private final Term mQuantClauseTerm;
	private final TermVariable[] mVars;
	private final Term[] mSubs;
	private final Term mInstClauseTerm;

	private final InstanceOrigin mOrigin;
	private final SourceAnnotation mSource;
	private final IProofTracker mProofTracker;

	/**
	 * Annotation for instances of quantified clauses.
	 *
	 * @param qClause
	 *            the quantified clause
	 * @param subs
	 *            the substitution producing the instance.
	 */
	public QuantAnnotation(final QuantClause qClause, final List<Term> subs, final Term instTerm,
			final InstanceOrigin origin) {
		mQuantClauseTerm = qClause.getClauseWithProof();
		mVars = qClause.getVars();
		mSubs = subs.toArray(new Term[subs.size()]);
		mInstClauseTerm = instTerm;
		mOrigin = origin;
		mSource = qClause.getQuantSource();
		mProofTracker = qClause.getQuantTheory().getClausifier().getTracker();
	}

	public SourceAnnotation getSource() {
		return mSource;
	}

	@Override
	public Term toTerm(final Clause cls, final Theory theory) {
		final Term quantClauseLitProof =
				mProofTracker.allIntro(mQuantClauseTerm, mVars);
		final Term quantClauseLit = mProofTracker.getProvedTerm(quantClauseLitProof);

		// For partial proofs, make an asserted sub proof for the quant clause.
		final Term subproof =
				mProofTracker instanceof ProofTracker ? ((ProofTracker) mProofTracker).getProof(quantClauseLitProof)
						: theory.term(ProofConstants.FN_ASSERTED, quantClauseLit);
		final Annotation[] clauseAnnots = new Annotation[] {
				new Annotation(ProofConstants.ANNOTKEY_PROVES, new Term[] { quantClauseLit }),
				new Annotation(ProofConstants.ANNOTKEY_INPUT,
						mSource.getAnnotation().isEmpty() ? null : mSource.getAnnotation()) };
		final Term quantUnitClauseProof = theory.term(ProofConstants.FN_CLAUSE,
				theory.annotatedTerm(clauseAnnots, subproof));

		final Term base = theory.or(theory.not(quantClauseLit), cls.toTerm(theory));

		final boolean isFullProofModeActive = mProofTracker instanceof ProofTracker;
		final Object[] subannots = new Object[isFullProofModeActive ? 5 : 3];
		subannots[0] = ":subs";
		subannots[1] = mSubs;
		subannots[2] = mOrigin.getOrigin();
		// In full proof mode, add proof for instance simplification.
		if (isFullProofModeActive) {
			subannots[3] = ":subproof";
			// Add the rewrite proof for substitutedformula = simplifiedformula
			subannots[4] = ((ProofTracker) mProofTracker).getProof(mInstClauseTerm);
		}

		final Annotation[] annots = new Annotation[] { new Annotation(":inst", subannots) };
		final Term instLemma = theory.term(ProofConstants.FN_LEMMA, theory.annotatedTerm(annots, base));

		final Term proofAnnot = theory.annotatedTerm(new Annotation[] { new Annotation(":pivot", quantClauseLit) },
				quantUnitClauseProof);
		return theory.term(ProofConstants.FN_RES, instLemma, proofAnnot);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(":inst ").append(mQuantClauseTerm.toString());
		sb.append(" :vars ").append(mVars.toString());
		sb.append(" :subs ").append(mSubs.toString());
		return sb.toString();
	}
}
