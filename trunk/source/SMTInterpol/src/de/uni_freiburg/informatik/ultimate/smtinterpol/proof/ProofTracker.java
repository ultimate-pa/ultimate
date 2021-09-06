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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This is an implementation of the IProofTracker that generates the proof annotations.
 *
 * @author Jochen Hoenicke
 */
public class ProofTracker implements IProofTracker{

	/**
	 * Create a proof tracker.
	 */
	public ProofTracker() {
	}

	public Term getProof(final Term t) {
		final Annotation[] annot = ((AnnotatedTerm) t).getAnnotations();
		assert annot.length == 1 && annot[0].getKey().equals(":proof");
		return (Term) annot[0].getValue();
	}

	private Term buildProof(final Term proof, final Term term) {
		assert proof != null;
		final Theory theory = term.getTheory();
		final Annotation[] annotions = new Annotation[] { new Annotation(":proof", proof) };
		return theory.annotatedTerm(annotions, term);
	}

	public Term quote(final Term atom) {
		final Theory t = atom.getTheory();
		return t.annotatedTerm(new Annotation[] { new Annotation(":quoted", null) }, atom);
	}

	@Override
	public Term intern(final Term term, final Term intern) {
		return buildRewrite(term, intern, ProofConstants.RW_INTERN);
	}

	@Override
	public Term flatten(final Term orig, final Set<Term> flattenedOrs) {
		final ArrayList<Term> flat = new ArrayList<>();
		final ArrayDeque<Term> todoStack = new ArrayDeque<>();
		final Term origTerm = getProvedTerm(orig);
		todoStack.addFirst(origTerm);
		while (!todoStack.isEmpty()) {
			final Term t = todoStack.removeFirst();
			if (flattenedOrs.contains(t)) {
				final ApplicationTerm appTerm = (ApplicationTerm) t;
				assert appTerm.getFunction().getName() == "or";
				final Term[] params = appTerm.getParameters();
				for (int i = params.length-1; i >= 0; i--) {
					todoStack.addFirst(params[i]);
				}
			} else {
				flat.add(t);
			}
		}
		Term result;
		if (flat.size() == 1) {
			result = flat.get(0);
		} else {
			result = orig.getTheory().term("or", flat.toArray(new Term[flat.size()]));
		}
		return transitivity(orig, buildRewrite(origTerm, result, ProofConstants.RW_FLATTEN));
	}

	@Override
	public Term orSimpClause(final Term rewrite) {
		final Theory t = rewrite.getTheory();
		final Term orig = getProvedTerm(rewrite);
		assert orig instanceof ApplicationTerm && ((ApplicationTerm) orig).getFunction() == t.mOr;
		final Term[] args = ((ApplicationTerm) orig).getParameters();
		final LinkedHashSet<Term> simpParams = new LinkedHashSet<>();
		for (final Term arg : args) {
			if (arg != t.mFalse) {
				simpParams.add(arg);
			}
		}
		Term result;
		if (simpParams.size() == 0) {
			result = t.mFalse;
		} else if (simpParams.size() == 1) {
			result = simpParams.iterator().next();
		} else {
			final Term[] newArgs = simpParams.toArray(new Term[simpParams.size()]);
			result = t.term("or", newArgs);
		}
		return transitivity(rewrite, buildRewrite(orig, result, ProofConstants.RW_OR_SIMP));
	}

	@Override
	public Term reflexivity(final Term a) {
		final Theory theory = a.getTheory();
		final Term proof = theory.term(ProofConstants.FN_REFL, a);
		return buildProof(proof, a);
	}

	private boolean isReflexivity(final Term proof) {
		return proof instanceof ApplicationTerm
				&& ((ApplicationTerm) proof).getFunction().getName() == ProofConstants.FN_REFL;
	}

	@Override
	public Term transitivity(final Term imp1, final Term imp2) {
		final Term proofImp1 = getProof(imp1);
		final Term proofImp2 = getProof(imp2);
		if (isReflexivity(proofImp1)) {
			return imp2;
		}
		if (isReflexivity(proofImp2)) {
			// reflexivity rule is used for internal rewrites that are not visible to the outside.
			// still we need to change the term
			return buildProof(proofImp1, getProvedTerm(imp2));
		}
		final Theory theory = imp1.getTheory();
		final Term proof = theory.term(ProofConstants.FN_TRANS, proofImp1, proofImp2);
		return buildProof(proof, getProvedTerm(imp2));
	}

	@Override
	public Term congruence(final Term a, final Term[] b) {
		final List<Term> congProofs = new ArrayList<>();
		congProofs.add(getProof(a));
		final Term[] params = new Term[b.length];
		for (int i = 0; i< b.length; i++) {
			final Term proofB = getProof(b[i]);
			if (!isReflexivity(proofB)) {
				congProofs.add(proofB);
			}
			params[i] = getProvedTerm(b[i]);
		}
		final Theory theory = a.getTheory();
		final ApplicationTerm aTerm = (ApplicationTerm) getProvedTerm(a);
		final Term proof;
		if (congProofs.size() == 1) {
			proof = congProofs.get(0);
		} else {
			proof = theory.term(ProofConstants.FN_CONG, congProofs.toArray(new Term[congProofs.size()]));
		}
		return buildProof(proof, theory.term(aTerm.getFunction(), params));
	}

	@Override
	public Term orMonotony(final Term a, final Term[] b) {
		assert b.length > 1;
		final List<Term> impProofs = new ArrayList<>();
		impProofs.add(getProof(a));
		final Term[] params = new Term[b.length];
		for (int i = 0; i < b.length; i++) {
			final Term proofB = getProof(b[i]);
			if (!isReflexivity(proofB)) {
				impProofs.add(proofB);
			}
			params[i] = getProvedTerm(b[i]);
		}
		final Theory theory = a.getTheory();
		final Term proof;
		if (impProofs.size() == 1) {
			proof = impProofs.get(0);
		} else {
			proof = theory.term(ProofConstants.FN_ORMONOTONY, impProofs.toArray(new Term[impProofs.size()]));
		}
		return buildProof(proof, theory.term("or", params));
	}

	@Override
	public Term modusPonens(final Term asserted, final Term simpFormula) {
		final Term simpProof = getProof(simpFormula);
		if (isReflexivity(simpProof)) {
			return buildProof(getProof(asserted), getProvedTerm(simpFormula));
		}
		final Theory t = asserted.getTheory();
		final Term proof = t.term(ProofConstants.FN_MP, getProof(asserted), simpProof);
		return buildProof(proof, getProvedTerm(simpFormula));
	}

	@Override
	public Term getClauseProof(final Term term) {
		return getProof(term);
	}

	@Override
	public Term auxAxiom(final Term axiom, final Annotation rule) {
		final Theory t = axiom.getTheory();
		final Term proof = t.term(ProofConstants.FN_TAUTOLOGY, t.annotatedTerm(new Annotation[] { rule }, axiom));
		return buildProof(proof, axiom);
	}

	@Override
	public Term split(final Term input, final Term splitTerm, final Annotation splitRule) {
		final Theory t = input.getTheory();
		final Term proof = t.term(ProofConstants.FN_SPLIT,
				t.annotatedTerm(new Annotation[] { splitRule }, getProof(input)), splitTerm);
		return buildProof(proof, splitTerm);
	}

	@Override
	public Term getProvedTerm(final Term t) {
		return ((AnnotatedTerm) t).getSubterm();
	}

	@Override
	public Term buildRewrite(final Term orig, final Term res, final Annotation rule) {
		final Theory theory = orig.getTheory();
		if (orig == res) {
			return reflexivity(res);
		}
		final Term statement = theory.term(rule.getKey() == ":removeForall" ? "=>" : "=", orig, res);
		final Annotation[] annot = new Annotation[] { rule };
		final Term proof = theory.term(ProofConstants.FN_REWRITE, theory.annotatedTerm(annot, statement));
		return buildProof(proof, res);
	}

	@Override
	public Term asserted(final Term formula) {
		final Theory theory = formula.getTheory();
		final Term proof = theory.term(ProofConstants.FN_ASSERTED, formula);
		return buildProof(proof, formula);
	}

	@Override
	public Term exists(final QuantifiedFormula quant, final Term newBody) {
		final Theory theory = quant.getTheory();
		final Term subProof = getProof(newBody);
		final Term formula = theory.exists(quant.getVariables(), getProvedTerm(newBody));
		if (isReflexivity(subProof)) {
			return reflexivity(formula);
		}
		final Annotation[] annot = new Annotation[] { new Annotation(":vars", quant.getVariables()) };
		final Term proof = theory.term(ProofConstants.FN_EXISTS, theory.annotatedTerm(annot, subProof));
		return buildProof(proof, formula);
	}

	@Override
	public Term forall(final QuantifiedFormula quant, final Term negNewBody) {
		final Theory theory = quant.getTheory();
		final Term negQuant = theory.term("not",
				theory.exists(quant.getVariables(), theory.term("not", quant.getSubformula())));
		Term rewrite = buildRewrite(quant, negQuant, ProofConstants.RW_FORALL_EXISTS);
		rewrite = congruence(rewrite, new Term[] { exists(quant, negNewBody) });
		return rewrite;
	}

	@Override
	public Term match(final MatchTerm oldMatch, final Term newData, final Term[] newCases) {
		final Theory theory = oldMatch.getTheory();
		final Term[] subProofs = new Term[newCases.length + 1];
		final Term[] newCaseTerms = new Term[newCases.length];
		subProofs[0] = getProof(newData);
		boolean isReflexivity = isReflexivity(subProofs[0]);
		for (int i = 0; i < newCases.length; i++) {
			final Annotation[] annot = new Annotation[] {
					new Annotation(":vars", oldMatch.getVariables()[i]),
					new Annotation(":constructor", oldMatch.getConstructors()[i])
			};
			final Term caseProof = getProof(newCases[i]);
			subProofs[i + 1] = theory.annotatedTerm(annot, caseProof);
			isReflexivity &= isReflexivity(caseProof);
			newCaseTerms[i] = getProvedTerm(newCases[i]);
		}
		final Term formula = theory.match(getProvedTerm(newData), oldMatch.getVariables(), newCaseTerms,
				oldMatch.getConstructors());
		if (isReflexivity) {
			return reflexivity(formula);
		}
		final Term proof = theory.term(ProofConstants.FN_MATCH, subProofs);
		return buildProof(proof, formula);
	}

	@Override
	public Term allIntro(final Term formula, final TermVariable[] vars) {
		final Theory theory = formula.getTheory();
		final Term subProof = getProof(formula);
		final Term body = getProvedTerm(formula);
		final Term quantified = theory.annotatedTerm(new Annotation[] { new Annotation(":quoted", null) },
				theory.forall(vars, body));
		final Annotation[] annot = new Annotation[] { new Annotation(":vars", vars) };
		final Term proof = theory.term(ProofConstants.FN_ALLINTRO, theory.annotatedTerm(annot, subProof));
		return buildProof(proof, quantified);
	}
}
