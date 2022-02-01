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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
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
	public Term flatten(final Term orig, final Set<Term> flattenedOrs) {
		/* nobody cares about this */
		return orig;
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
	public Term orMonotony(Term a, Term[] b) {
		assert a instanceof ApplicationTerm && ((ApplicationTerm) a).getFunction().getName() == "or";
		assert b.length > 1;
		final Theory theory = a.getSort().getTheory();
		return theory.term("or", b);
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
	public Term auxAxiom(final Term axiom, final Annotation auxRule) {
		return axiom;
	}

	@Override
	public Term split(final Term input, final Term splitTerm, final Annotation splitKind) {
		return splitTerm;
	}

	@Override
	public Term asserted(final Term formula) {
		return formula;
	}

	@Override
	public Term exists(final QuantifiedFormula quant, final Term newBody) {
		final Theory theory = quant.getTheory();
		return theory.exists(quant.getVariables(), newBody);
	}
	@Override
	public Term forall(final QuantifiedFormula quant, final Term negNewBody) {
		final Theory theory = quant.getTheory();
		return theory.term("not", theory.exists(quant.getVariables(), negNewBody));
	}

	@Override
	public Term allIntro(Term formula, TermVariable[] vars) {
		final Theory theory = formula.getTheory();
		return theory.annotatedTerm(new Annotation[] { new Annotation(":quoted", null) },
				theory.forall(vars, formula));
	}
}
