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

import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This is an implementation of the IProofTracker that generates the proof
 * annotations.
 *
 * @author Jochen Hoenicke
 */
public class ProofTracker implements IProofTracker {

	ProofRules mProofRules;

	/**
	 * Create a proof tracker.
	 */
	public ProofTracker(Theory theory) {
		mProofRules = new ProofRules(theory);
		setupTheory(theory);
	}

	private void setupTheory(Theory theory) {
		if (theory.getDeclaredSorts().containsKey(ProofConstants.SORT_EQPROOF)) {
			return;
		}

		theory.declareInternalSort(ProofConstants.SORT_EQPROOF, 1, 0);
		final Sort[] generic = theory.createSortVariables("X");
		final Sort eqProofX = theory.getSort(ProofConstants.SORT_EQPROOF, generic[0]);
		final Sort eqProofBool = theory.getSort(ProofConstants.SORT_EQPROOF, theory.getBooleanSort());
		final Sort[] generic2 = new Sort[] { generic[0], generic[0] };
		final Sort[] eqProofX2 = new Sort[] { eqProofX, eqProofX };

		// Rewrite proofs.
		theory.declareInternalPolymorphicFunction(ProofConstants.FN_REFL, generic, generic,
				eqProofX, 0);
		theory.declareInternalPolymorphicFunction(ProofConstants.FN_REWRITE, generic, generic2, eqProofX, 0);
		theory.declareInternalPolymorphicFunction(ProofConstants.FN_TRANS, generic, eqProofX2, eqProofX,
				FunctionSymbol.LEFTASSOC);
		theory.declareInternalFunctionFactory(new CongRewriteFunctionFactory());
		theory.declareInternalFunctionFactory(new MatchRewriteFunctionFactory());
		theory.declareInternalFunction(ProofConstants.FN_QUANT, new Sort[] { eqProofBool }, eqProofBool, 0);
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

	@Override
	public Term intern(final Term term, final Term intern) {
		return buildRewrite(term, intern, ProofConstants.RW_INTERN);
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
		return isApplication(ProofConstants.FN_REFL, proof);
	}

	@Override
	public Term transitivity(final Term imp1, final Term imp2) {
		final Term proofImp1 = getProof(imp1);
		final Term proofImp2 = getProof(imp2);
		if (isReflexivity(proofImp1)) {
			return imp2;
		}
		if (isReflexivity(proofImp2)) {
			// reflexivity rule is used for internal rewrites that are not visible to the
			// outside.
			// still we need to change the term
			return buildProof(proofImp1, getProvedTerm(imp2));
		}
		final Theory theory = imp1.getTheory();
		final Term proof = theory.term(ProofConstants.FN_TRANS, proofImp1, proofImp2);
		return buildProof(proof, getProvedTerm(imp2));
	}

	@Override
	public Term congruence(final Term a, final Term[] b) {
		final Term[] proofs = new Term[b.length];
		final Term[] params = new Term[b.length];
		boolean isRefl = true;
		for (int i = 0; i < b.length; i++) {
			proofs[i] = getProof(b[i]);
			params[i] = getProvedTerm(b[i]);
			if (!isReflexivity(proofs[i])) {
				isRefl = false;
			}
		}
		final Theory theory = a.getTheory();
		final ApplicationTerm aTerm = (ApplicationTerm) getProvedTerm(a);
		final FunctionSymbol aFunc = aTerm.getFunction();
		final Term provedTerm = theory.term(aFunc, params);
		Term congProof;
		if (isRefl) {
			congProof = reflexivity(provedTerm);
		} else {
			final String[] aIndices = aFunc.getIndices();
			final String[] indices = new String[aIndices == null ? 1 : 1 + aIndices.length];
			indices[0] = aFunc.getName();
			if (aIndices != null) {
				System.arraycopy(aIndices, 0, indices, 1, aIndices.length);
			}
			final Sort resultSort = aFunc.isReturnOverload()
					? theory.getSort(ProofConstants.SORT_EQPROOF, aFunc.getReturnSort())
					: null;
			congProof = buildProof(theory.term(ProofConstants.FN_CONG, indices, resultSort, proofs), provedTerm);
		}
		final Term proof = transitivity(a, congProof);
		return proof;
	}

	/**
	 * Create a proof of {~lhs, rhs} from a rewrite proof {@code (= lhs rhs)} for
	 * rhs.
	 *
	 * @param lhs
	 *            the rewritten literal.
	 * @param rewrite
	 *            the simplified formula rhs annotated with a proof of
	 *            {@code (= lhs rhs)}.
	 * @return the clause proving {~lhs, rhs}
	 */
	@Override
	public Term rewriteToClause(Term lhs, Term rewrite) {
		if (isReflexivity(getProof(rewrite))) {
			return null;
		}
		final ProofLiteral[] lits = new ProofLiteral[] {
				termToProofLiteral(lhs).negate(),
				termToProofLiteral(getProvedTerm(rewrite))
		};
		final Annotation[] annots = new Annotation[] {
				new Annotation(ProofConstants.ANNOTKEY_REWRITE, getProof(rewrite))
		};
		return buildProof(mProofRules.oracle(lits, annots), getProvedTerm(rewrite));
	}

	public Term resolve(Term pivotLit, final Term posClause, final Term negClause) {
		boolean positive = true;
		while (isApplication(SMTLIBConstants.NOT, pivotLit)) {
			pivotLit = ((ApplicationTerm) pivotLit).getParameters()[0];
			positive = !positive;
		}
		return mProofRules.resolutionRule(pivotLit, positive ? posClause : negClause, positive ? negClause : posClause);
	}

	@Override
	public Term resolveBinaryTautology(final Term asserted, final Term conclusion, final Annotation rule) {
		final Theory theory = asserted.getTheory();
		boolean isPositive = true;
		final Term assertedTerm = getProvedTerm(asserted);
		Term assertedAtom = assertedTerm;
		while (isApplication(SMTLIBConstants.NOT, assertedAtom)) {
			assertedAtom = ((ApplicationTerm) assertedAtom).getParameters()[0];
			isPositive = !isPositive;
		}
		final Term negAsserted = isPositive ? theory.term(SMTLIBConstants.NOT, assertedAtom) : assertedAtom;
		final Term taut = tautology(theory.term(SMTLIBConstants.OR, negAsserted, conclusion), rule);
		final Term proof = resolve(assertedTerm, getProof(asserted), getProof(taut));
		return buildProof(proof, conclusion);
	}

	@Override
	public Term modusPonens(final Term asserted, final Term rewrite) {
		if (isReflexivity(getProof(rewrite))) {
			return buildProof(getProof(asserted), getProvedTerm(rewrite));
		}
		final Term assertedTerm = getProvedTerm(asserted);
		final Term proof = resolve(assertedTerm, getProof(asserted), getProof(rewriteToClause(assertedTerm, rewrite)));
		return buildProof(proof, getProvedTerm(rewrite));
	}

	@Override
	public Term getClauseProof(final Term term) {
		return getProof(term);
	}

	@Override
	public Term tautology(final Term axiom, final Annotation rule) {
		final Term proof = mProofRules.oracle(termToProofLiterals(axiom), new Annotation[] { rule });
		return buildProof(proof, axiom);
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
		final Annotation[] annot = new Annotation[] { rule };
		final Term proof = theory.term(ProofConstants.FN_REWRITE, theory.annotatedTerm(annot, orig), res);
		return buildProof(proof, res);
	}

	@Override
	public Term asserted(Term formula) {
		Term proof = mProofRules.asserted(formula);
		// Apply not elimination to extract literal
		boolean positive = true;
		while (isApplication(SMTLIBConstants.NOT, formula)) {
			proof = mProofRules.resolutionRule(formula, positive ? proof : mProofRules.notIntro(formula),
					positive ? mProofRules.notElim(formula) : proof);
			positive = !positive;
			formula = ((ApplicationTerm) formula).getParameters()[0];
		}
		return buildProof(proof, positive ? formula : formula.getTheory().term(SMTLIBConstants.NOT, formula));
	}

	@Override
	public Term quantCong(final QuantifiedFormula quant, final Term newBody) {
		final Theory theory = quant.getTheory();
		final Term subProof = getProof(newBody);
		final boolean isForall = quant.getQuantifier() == QuantifiedFormula.FORALL;
		final Term formula = isForall ? theory.forall(quant.getVariables(), getProvedTerm(newBody))
				: theory.exists(quant.getVariables(), getProvedTerm(newBody));
		if (isReflexivity(subProof)) {
			return reflexivity(formula);
		}
		final String quantType = isForall ? ":forall" : ":exists";
		final Annotation[] annot = new Annotation[] { new Annotation(quantType, quant.getVariables()) };
		final Term proof = theory.term(ProofConstants.FN_QUANT, theory.annotatedTerm(annot, subProof));
		return buildProof(proof, formula);
	}

	@Override
	public Term match(final MatchTerm oldMatch, final Term newData, final Term[] newCases) {
		final Theory theory = oldMatch.getTheory();
		final Term[] subProofs = new Term[newCases.length + 1];
		final Term[] newCaseTerms = new Term[newCases.length];
		final Constructor[] constrs = oldMatch.getConstructors();
		subProofs[0] = getProof(newData);
		boolean isReflexivity = isReflexivity(subProofs[0]);
		for (int i = 0; i < newCases.length; i++) {
			final String constructorName = constrs[i] == null ? null : constrs[i].getName();
			final Annotation[] annot = new Annotation[] {
					new Annotation(ProofConstants.ANNOTKEY_VARS, oldMatch.getVariables()[i]),
					new Annotation(ProofConstants.ANNOTKEY_CONSTRUCTOR, constructorName) };
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
		final Term provedClause = getProvedTerm(formula);
		Term proof = getProof(formula);
		if (isApplication("not", provedClause)) {
			final Term atom = ((ApplicationTerm) provedClause).getParameters()[0];
			proof = mProofRules.resolutionRule(atom, mProofRules.notIntro(provedClause), proof);
		}
		final Term[] skolemTerms = mProofRules.getSkolemVars(vars, provedClause, true);
		proof = theory.let(vars, skolemTerms, proof);
		final Term lettedClause = theory.let(vars, skolemTerms, provedClause);
		final FormulaUnLet unletter = new FormulaUnLet();
		proof = unletter.unlet(proof);
		/* compute the resulting quantified term (forall (...) origTerm) */
		final Term forallAtom = theory.forall(vars, provedClause);
		proof = mProofRules.resolutionRule(unletter.unlet(lettedClause), proof,
				mProofRules.forallIntro((QuantifiedFormula) forallAtom));
		return buildProof(proof, forallAtom);
	}

	/**
	 * Checks if a term is an application of an internal function symbol.
	 *
	 * @param funcSym
	 *            the expected function symbol.
	 * @param term
	 *            the term to check.
	 * @return true if term is an application of funcSym.
	 */
	private boolean isApplication(final String funcSym, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern() && func.getName().equals(funcSym)) {
				return true;
			}
		}
		return false;
	}

	private ProofLiteral termToProofLiteral(Term term) {
		boolean isPositive = true;
		while (isApplication(SMTLIBConstants.NOT, term)) {
			term = ((ApplicationTerm) term).getParameters()[0];
			isPositive = !isPositive;
		}
		return new ProofLiteral(term, isPositive);
	}

	/**
	 * Convert a clause term into an Array of terms, one entry for each disjunct.
	 * This also handles singleton and empty clause correctly.
	 *
	 * @param clauseTerm
	 *            The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private Term[] termToClause(final Term clauseTerm) {
		assert clauseTerm != null && clauseTerm.getSort().getName() == "Bool";
		if (isApplication("or", clauseTerm)) {
			return ((ApplicationTerm) clauseTerm).getParameters();
		} else if (isApplication("false", clauseTerm)) {
			return new Term[0];
		} else {
			/* in all other cases, this is a singleton clause. */
			return new Term[] { clauseTerm };
		}
	}

	/**
	 * Convert an array of terms into an array of proof literals, one entry for each
	 * disjunct. This also removes double negations.
	 *
	 * @param clauseTerm
	 *            The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private ProofLiteral[] termArrayToProofLiterals(final Term[] clauseLits) {
		final ProofLiteral[] proofLits = new ProofLiteral[clauseLits.length];
		for (int i = 0; i < proofLits.length; i++) {
			proofLits[i] = termToProofLiteral(clauseLits[i]);
		}
		return proofLits;
	}

	/**
	 * Convert a clause term into an array of proof literals, one entry for each
	 * disjunct. This also removes double negations.
	 *
	 * @param clauseTerm
	 *            The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private ProofLiteral[] termToProofLiterals(final Term clauseTerm) {
		return termArrayToProofLiterals(termToClause(clauseTerm));
	}

}
