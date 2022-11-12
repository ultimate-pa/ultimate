/*
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This is an implementation of the IProofTracker that doesn't generated the proof annotations. It still applies some of
 * the rules to create the right result term, but it doesn't track the proof.
 *
 * @author Jochen Hoenicke
 */
public class NoopProofTracker implements IProofTracker {

	/**
	 * Create a dummy proof tracker for the case that proofs are not necessary.
	 */
	public NoopProofTracker() {
	}

	@Override
	public Term buildRewrite(final Term orig, final Term res, final Annotation rule) {
		return res;
	}

	@Override
	public Term intern(final Term orig, final Term res) {
		return res;
	}

	@Override
	public Term orSimpClause(final Term rewrite) {
		return rewrite;
	}

	@Override
	public Term reflexivity(final Term a) {
		return a;
	}

	@Override
	public Term transitivity(final Term a, final Term b) {
		return b;
	}

	@Override
	public Term congruence(final Term a, final Term[] b) {
		final Theory theory = a.getSort().getTheory();
		final FunctionSymbol func = ((ApplicationTerm) a).getFunction();
		return theory.term(func, b);
	}

	@Override
	public Term modusPonens(final Term asserted, final Term simpFormula) {
		return simpFormula;
	}

	@Override
	public Term getClauseProof(final Term term) {
		return null;
	}

	@Override
	public Term getProvedTerm(final Term t) {
		return t;
	}

	@Override
	public Term tautology(final Term axiom, final Annotation auxRule) {
		return axiom;
	}

	@Override
	public Term asserted(final Term formula) {
		return formula;
	}

	@Override
	public Term quantCong(final QuantifiedFormula quant, final Term newBody) {
		final Theory theory = quant.getTheory();
		final boolean isForall = quant.getQuantifier() == QuantifiedFormula.FORALL;
		return isForall ? theory.forall(quant.getVariables(), getProvedTerm(newBody))
				: theory.exists(quant.getVariables(), getProvedTerm(newBody));
	}

	@Override
	public Term match(final MatchTerm oldMatch, final Term newData, final Term[] newCases) {
		final Theory theory = oldMatch.getTheory();
		return theory.match(newData, oldMatch.getVariables(), newCases, oldMatch.getConstructors());
	}

	@Override
	public Term allIntro(final Term formula, final TermVariable[] vars) {
		final Theory theory = formula.getTheory();
		return theory.forall(vars, formula);
	}

	@Override
	public Term resolveBinaryTautology(Term asserted, Term conclusion, Annotation tautRule) {
		return conclusion;
	}

	@Override
	public Term rewriteToClause(Term lhs, Term rewrite) {
		return null;
	}
}
