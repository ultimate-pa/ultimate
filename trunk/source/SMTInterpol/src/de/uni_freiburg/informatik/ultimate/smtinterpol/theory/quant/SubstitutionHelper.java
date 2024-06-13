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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermCompiler;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * Helper class for substitution in quantified clauses.
 *
 * @author Tanja Schindler
 *
 */
public class SubstitutionHelper {

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;
	private final IProofTracker mTracker;

	private final Literal[] mGroundLits;
	private final QuantLiteral[] mQuantLits;
	private final SourceAnnotation mSource;
	private final Map<TermVariable, Term> mSigma;

	public SubstitutionHelper(final QuantifierTheory quantTheory, final Literal[] groundLits,
			final QuantLiteral[] quantLits, final SourceAnnotation source, final Map<TermVariable, Term> sigma) {
		mQuantTheory = quantTheory;
		mClausifier = mQuantTheory.getClausifier();
		mTracker = mClausifier.getTracker();
		mGroundLits = groundLits;
		mQuantLits = quantLits;
		mSource = source;
		mSigma = sigma;
	}

	/**
	 * Apply the given substitution to the given clause. The resulting literals and the corresponding term can be
	 * retrieved afterwards.
	 *
	 * This method also performs simplifications on literals and on the clause. The steps are:<br>
	 * (1) Apply the substitution for the single literals, normalize and simplify the terms.<br>
	 * (2) Build the disjunction.<br>
	 * (3) Remove duplicates and false literals.<br>
	 * (4) Build the actual literals.
	 *
	 * @return the result of the substitution and simplification.
	 */
	public SubstitutionResult substituteInClause() {

		assert !mSigma.isEmpty();

		final List<Term> substitutedLitTerms = new ArrayList<>(mGroundLits.length + mQuantLits.length);
		final List<Term> provedLitTerms = new ArrayList<>(mGroundLits.length + mQuantLits.length);
		// We also need duplicates here for proof production.
		final Set<ILiteral> resultingGroundLits = new LinkedHashSet<>();
		final Set<ILiteral> resultingQuantLits = new LinkedHashSet<>();

		final Theory theory = mQuantTheory.getTheory();

		// Ground literals remain unchanged.
		for (final Literal gLit : mGroundLits) {
			final Term groundLitTerm = gLit.getSMTFormula(theory);
			substitutedLitTerms.add(groundLitTerm);
			provedLitTerms.add(mTracker.reflexivity(groundLitTerm));
			resultingGroundLits.add(gLit);
		}

		// Substitute in quantified literals
		for (final QuantLiteral qLit : mQuantLits) {
			if (Collections.disjoint(Arrays.asList(qLit.getTerm().getFreeVars()), mSigma.keySet())) {
				// Nothing to substitute.
				substitutedLitTerms.add(qLit.getSMTFormula(theory));
				provedLitTerms.add(mTracker.reflexivity(qLit.getSMTFormula(theory)));
				resultingQuantLits.add(qLit);
			} else { // Build the new literals. Separate ground and quantified literals.

				// Substitute variables.
				final FormulaUnLet unletter = new FormulaUnLet();
				unletter.addSubstitutions(mSigma);
				final Term substituted = unletter.transform(qLit.getSMTFormula(theory));
				substitutedLitTerms.add(substituted);

				Term simplified = normalizeAndSimplifyLitTerm(substituted);

				if (mTracker.getProvedTerm(simplified) == theory.mTrue) { // Clause is trivially true.
					return buildTrueResult();
				}
				if (mTracker.getProvedTerm(simplified) == theory.mFalse) {
					provedLitTerms.add(simplified);
					continue;
				}

				final ILiteral newAtom;
				boolean isPos = true;
				Term atomTerm = mTracker.getProvedTerm(simplified);
				assert atomTerm instanceof ApplicationTerm;
				if (((ApplicationTerm) atomTerm).getFunction().getName() == "not") {
					atomTerm = ((ApplicationTerm) atomTerm).getParameters()[0];
					isPos = false;
				}
				assert atomTerm instanceof ApplicationTerm;
				final ApplicationTerm atomApp = (ApplicationTerm) atomTerm;
				if (atomApp.getFunction().getName() == "<=") {
					if (atomApp.getFreeVars().length == 0) {
						final Polynomial lhs = new Polynomial(atomApp.getParameters()[0]);
						final MutableAffineTerm msum =
								mClausifier.createMutableAffinTerm(lhs, mSource);
						newAtom = mQuantTheory.getLinAr().generateConstraint(msum, false);
					} else {
						newAtom = mQuantTheory.getQuantInequality(isPos, atomApp.getParameters()[0], mSource);
					}
				} else if (atomApp.getFunction().getName() == "=") {
					final Term lhs = atomApp.getParameters()[0];
					final Term rhs = atomApp.getParameters()[1];
					if (atomApp.getFreeVars().length == 0) { // Ground equality or predicate.
						final EqualityProxy eq = mClausifier.createEqualityProxy(lhs, rhs, mSource);
						assert eq != EqualityProxy.getTrueProxy() && eq != EqualityProxy.getFalseProxy();
						newAtom = eq.getLiteral(mSource);
					} else {
						newAtom = mQuantTheory.getQuantEquality(atomApp.getParameters()[0], atomApp.getParameters()[1],
								mSource);
					}
				} else { // Predicates
					assert atomApp.getFreeVars().length == 0; // Quantified predicates are stored as equalities.
					assert atomApp.getSort() == theory.getBooleanSort();
					final Term sharedLhs = atomApp;
					final Term sharedRhs = theory.mTrue;
					final EqualityProxy eq = mClausifier.createEqualityProxy(sharedLhs, sharedRhs, mSource);
					assert eq != EqualityProxy.getTrueProxy() && eq != EqualityProxy.getFalseProxy();
					newAtom = eq.getLiteral(mSource);
				}
				// As in clausifier
				final Term atomIntern = mTracker.intern(atomApp, newAtom.getSMTFormula(theory));
				if (isPos) {
					simplified = mTracker.transitivity(simplified, atomIntern);
				} else {
					simplified = mTracker.congruence(simplified, new Term[] { atomIntern });
					/* (not (<= -x 0)) can be rewritten to (not (not (< x 0))); remove double negation */
					simplified = mClausifier.getSimplifier().convertNot(simplified);
				}
				provedLitTerms.add(simplified);

				final ILiteral newLiteral = isPos ? newAtom : newAtom.negate();
				if (newLiteral instanceof Literal) {
					final Literal newGroundLit = (Literal) newLiteral;
					if (resultingGroundLits.contains(newGroundLit.negate())) { // Clause simplifies to true
						return buildTrueResult();
					} else {
						resultingGroundLits.add(newGroundLit);
					}
				} else {
					final QuantLiteral newQuantLit = (QuantLiteral) newLiteral;
					if (resultingQuantLits.contains(newQuantLit.negate())) { // Clause simplifies to true
						return buildTrueResult();
					} else {
						resultingQuantLits.add(newQuantLit);
					}
				}
			}
		}

		// Build the disjunction.
		final boolean isUnitClause = substitutedLitTerms.size() == 1;
		final Term substitutedClause = isUnitClause ? substitutedLitTerms.get(0)
				: theory.term("or", substitutedLitTerms.toArray(new Term[substitutedLitTerms.size()]));
		Term simpClause;
		if (isUnitClause) {
			assert provedLitTerms.size() == 1;
			simpClause = provedLitTerms.get(0);
		} else {
			simpClause = mTracker.congruence(mTracker.reflexivity(substitutedClause),
					provedLitTerms.toArray(new Term[provedLitTerms.size()]));
			simpClause = mTracker.orSimpClause(simpClause);
		}
		return new SubstitutionResult(substitutedClause, simpClause,
				resultingGroundLits.toArray(new Literal[resultingGroundLits.size()]),
				resultingQuantLits.toArray(new QuantLiteral[resultingQuantLits.size()]));
	}

	/**
	 * Normalize an equality or inequality literal term.
	 *
	 * @return the simplified term and its rewrite proof.
	 */
	private Term normalizeAndSimplifyLitTerm(final Term litTerm) {
		final Theory theory = mQuantTheory.getTheory();

		final boolean isNegated = litTerm instanceof ApplicationTerm
				&& ((ApplicationTerm) litTerm).getFunction().getName() == "not";
		final ApplicationTerm atomTerm = (ApplicationTerm) (isNegated ? ((ApplicationTerm) litTerm).getParameters()[0]
				: litTerm);
		final Term atomRewrite = mTracker.reflexivity(atomTerm);
		assert atomTerm.getFunction().getName() == "<=" || atomTerm.getFunction().getName() == "=";
		final TermCompiler compiler = mClausifier.getTermCompiler();

		// Term compiler normalizes and simplifies <= literals.
		if (atomTerm.getFunction().getName() == "<=") {
			return compiler.transform(litTerm);
		}

		// Other quantified literals are equalities
		assert atomTerm.getFunction().getName() == "=";
		final Term lhs = atomTerm.getParameters()[0];
		final Term rhs = atomTerm.getParameters()[1];
		Term normalizedAtom;
		if (QuantUtil.isAuxApplication(lhs)) {
			final Term[] params = ((ApplicationTerm) lhs).getParameters();
			final Term[] normalizedParams = new Term[params.length];
			for (int i = 0; i < normalizedParams.length; i++) {
				normalizedParams[i] = compiler.transform(params[i]);
			}
			final Term normalizedAux = mTracker.congruence(mTracker.reflexivity(lhs), normalizedParams);
			normalizedAtom = mTracker.congruence(atomRewrite, new Term[] { normalizedAux, mTracker.reflexivity(rhs) });
		} else {
			// Normalize lhs and rhs separately
			final Term normalizedLhs = compiler.transform(lhs);
			final Term normalizedRhs = compiler.transform(rhs);
			normalizedAtom = mTracker.congruence(atomRewrite, new Term[] { normalizedLhs, normalizedRhs });

			// Simplify equality literals similar to EqualityProxy.
			final Term trivialEq = Clausifier.checkAndGetTrivialEquality(mTracker.getProvedTerm(normalizedLhs),
					mTracker.getProvedTerm(normalizedRhs), theory);
			if (trivialEq != null) {
				normalizedAtom = mTracker.transitivity(normalizedAtom,
						mTracker.intern(mTracker.getProvedTerm(normalizedAtom), trivialEq));
			}
		}
		if (isNegated) {
			return mClausifier.getSimplifier()
					.convertNot(mTracker.congruence(mTracker.reflexivity(litTerm), new Term[] { normalizedAtom }));
		}
		return normalizedAtom;
	}

	private SubstitutionResult buildTrueResult() {
		return new SubstitutionResult(null, null, null, null);
	}

	/**
	 * This class is used to collect the result from substituting variables in a clause. It contains information about
	 * the substituted clause term, the simplified substituted term, and the corresponding literals.
	 */
	static class SubstitutionResult {
		final Term mSubstituted;
		final Term mSimplified;
		final Literal[] mGroundLits;
		final QuantLiteral[] mQuantLits;

		/**
		 * Build a new SubstitutionResult.
		 *
		 * @param substituted
		 *            the substituted term.
		 * @param simplified
		 *            the simplified term, potentially annotated with a proof that it equals the substituted term
		 * @param groundLits
		 *            the resulting ground literals
		 * @param quantLits
		 *            the resulting quantified literals
		 */
		protected SubstitutionResult(final Term substituted, final Term simplified, final Literal[] groundLits,
				final QuantLiteral[] quantLits) {
			mSubstituted = substituted;
			mSimplified = simplified;
			mGroundLits = groundLits;
			mQuantLits = quantLits;
		}

		public boolean isTriviallyTrue() {
			return mSimplified == null;
		}

		public boolean isGround() {
			return isTriviallyTrue() || mQuantLits.length == 0;
		}

		public Term getSubstituted() {
			return mSubstituted;
		}

		public Term getSimplified() {
			return mSimplified;
		}

		public Literal[] getGroundLits() {
			return mGroundLits;
		}

		public QuantLiteral[] getQuantLits() {
			return mQuantLits;
		}
	}
}
