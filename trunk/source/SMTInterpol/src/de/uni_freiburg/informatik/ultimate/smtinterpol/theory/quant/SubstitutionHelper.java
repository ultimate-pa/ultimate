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
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermCompiler;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;

/**
 * Helper class for substitution in quantified clauses.
 * 
 * @author Tanja Schindler
 *
 */
public class SubstitutionHelper {

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;
	private final Literal[] mGroundLits;
	private final QuantLiteral[] mQuantLits;
	private final SourceAnnotation mSource;
	private final Map<TermVariable, Term> mSigma;
	private Literal[] mResultingGroundLits;
	private QuantLiteral[] mResultingQuantLits;
	private Term mResultingClauseTerm;

	public SubstitutionHelper(final QuantifierTheory quantTheory, final Literal[] groundLits,
			final QuantLiteral[] quantLits, final SourceAnnotation source, final Map<TermVariable, Term> sigma) {
		mQuantTheory = quantTheory;
		mClausifier = quantTheory.getClausifier();
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
	 * (2) Build the disjunction ---> Proof rules cong, refl, etc. <br>
	 * (3) Remove duplicates and false literals ---> Proof rule simpOr. <br>
	 * (4) Build the actual literals.
	 * 
	 * TODO Proof production.
	 */
	public void substituteInClause() {

		assert !mSigma.isEmpty();

		final List<Term> substitutedLitTerms = new ArrayList<>(mGroundLits.length + mQuantLits.length);
		// We also need duplicates here for proof production.
		final Set<ILiteral> resultingGroundLits = new LinkedHashSet<>();
		final Set<ILiteral> resultingQuantLits = new LinkedHashSet<>();

		// Ground literals remain unchanged.
		for (final Literal gLit : mGroundLits) {
			final Term groundLitTerm = gLit.getSMTFormula(mQuantTheory.getTheory()); // TODO quoted ?
			substitutedLitTerms.add(groundLitTerm);
			resultingGroundLits.add(gLit);
		}

		// Substitute in quantified literals
		for (final QuantLiteral qLit : mQuantLits) {
			if (Collections.disjoint(Arrays.asList(qLit.getTerm().getFreeVars()), mSigma.keySet())) {
				// Nothing to substitute.
				substitutedLitTerms.add(qLit.getTerm());
				resultingQuantLits.add(qLit);
			} else { // Build the new literals. Separate ground and quantified literals.
				final Term subsLitTerm = computeSubstitutedLiteralAsTerm(qLit, mSigma);
				if (subsLitTerm == mQuantTheory.getTheory().mTrue) { // Clause is trivially true.
					mResultingGroundLits = null;
					mResultingQuantLits = null;
					mResultingClauseTerm = mQuantTheory.getTheory().mTrue;
					return;
				}

				substitutedLitTerms.add(subsLitTerm);
				if (subsLitTerm == mQuantTheory.getTheory().mFalse) {
					continue;
				}
				final ILiteral newAtom;
				boolean isPos = true;
				Term atomTerm = subsLitTerm;
				assert subsLitTerm instanceof ApplicationTerm;
				if (((ApplicationTerm) subsLitTerm).getFunction().getName() == "not") {
					atomTerm = ((ApplicationTerm) subsLitTerm).getParameters()[0];
					isPos = false;
				}
				assert atomTerm instanceof ApplicationTerm;
				final ApplicationTerm atomApp = (ApplicationTerm) atomTerm;
				if (atomApp.getFunction().getName() == "<=") {
					if (atomApp.getFreeVars().length == 0) {
						final SMTAffineTerm lhs = new SMTAffineTerm(atomApp.getParameters()[0]);
						final MutableAffineTerm msum =
								mClausifier.createMutableAffinTerm(lhs, mSource);
						newAtom = mQuantTheory.getLinAr().generateConstraint(msum, false);
					} else {
						newAtom = mQuantTheory.getQuantInequality(isPos, mSource, atomApp.getParameters()[0]);
					}
				} else if (atomApp.getFunction().getName() == "=") {
					final Term lhs = atomApp.getParameters()[0];
					final Term rhs = atomApp.getParameters()[1];
					if (atomApp.getFreeVars().length == 0) { // Ground equality or predicate.
						final SharedTerm sharedLhs = mClausifier.getSharedTerm(lhs, mSource);
						final SharedTerm sharedRhs = mClausifier.getSharedTerm(rhs, mSource);
						final EqualityProxy eq = mClausifier.createEqualityProxy(sharedLhs, sharedRhs);
						assert eq != EqualityProxy.getTrueProxy() && eq != EqualityProxy.getFalseProxy();
						newAtom = eq.getLiteral(mSource);
					} else {
						newAtom = mQuantTheory.getQuantEquality(isPos, mSource, atomApp.getParameters()[0],
								atomApp.getParameters()[1]);
					}
				} else { // Predicates
					assert atomApp.getFreeVars().length == 0; // Quantified predicates are stored as equalities.
					assert atomApp.getSort() == mQuantTheory.getTheory().getBooleanSort();
					final SharedTerm sharedLhs = mClausifier.getSharedTerm(atomApp, mSource);
					final SharedTerm sharedRhs =
							mClausifier.getSharedTerm(mQuantTheory.getTheory().mTrue, mSource);
					final EqualityProxy eq = mClausifier.createEqualityProxy(sharedLhs, sharedRhs);
					assert eq != EqualityProxy.getTrueProxy() && eq != EqualityProxy.getFalseProxy();
					newAtom = eq.getLiteral(mSource);
				}
				final ILiteral newLiteral = isPos ? newAtom : newAtom.negate();
				if (newLiteral instanceof Literal) {
					final Literal newGroundLit = (Literal) newLiteral;
					if (resultingGroundLits.contains(newGroundLit.negate())) { // Clause simplifies to true
						mResultingGroundLits = null;
						mResultingQuantLits = null;
						mResultingClauseTerm = mQuantTheory.getTheory().mTrue;
						return;
					} else {
						resultingGroundLits.add(newGroundLit);
					}
				} else {
					final QuantLiteral newQuantLit = (QuantLiteral) newLiteral;
					if (resultingQuantLits.contains(newQuantLit.negate())) { // Clause simplifies to true
						mResultingGroundLits = null;
						mResultingQuantLits = null;
						mResultingClauseTerm = mQuantTheory.getTheory().mTrue;
						return;
					} else {
						resultingQuantLits.add(newQuantLit);
					}
				}
			}
		}
		// Build the disjunction.
		final Term disjunctionOfSubstitutedLits =
				mQuantTheory.getTheory().term("or", substitutedLitTerms.toArray(new Term[substitutedLitTerms.size()]));
		// TODO Proof production.

		mResultingGroundLits = resultingGroundLits.toArray(new Literal[resultingGroundLits.size()]);
		mResultingQuantLits = resultingQuantLits.toArray(new QuantLiteral[resultingQuantLits.size()]);

		// Build the corresponding term.
		final Term[] resultingLitTerms = new Term[mResultingGroundLits.length + mResultingQuantLits.length];
		int i = 0;
		for (; i < mResultingGroundLits.length; i++) {
			// TODO quoted?
			resultingLitTerms[i] = mResultingGroundLits[i].getSMTFormula(mQuantTheory.getTheory(), false);
		}
		for (int j = 0; j < mResultingQuantLits.length; j++) {
			// TODO quoted?
			resultingLitTerms[i + j] = mResultingQuantLits[j].getSMTFormula(mQuantTheory.getTheory(), false); // quoted?
		}
		mResultingClauseTerm = mQuantTheory.getTheory().or(resultingLitTerms);
		// TODO Proof production.
	}

	/**
	 * After applying the substitution, get the resulting ground literals.
	 * 
	 * @return An array, possibly of length 0, containing the resulting ground literals if the clause is not simplified
	 *         to true; null if the clause is simplified to true.
	 */
	public Literal[] getResultingGroundLits() {
		assert mResultingClauseTerm != null : "Quant: Substitution has not yet been performed.";
		return mResultingGroundLits;
	}

	/**
	 * After applying the substitution, get the resulting quantified literals.
	 * 
	 * @return An array, possibly of length 0, containing the resulting quantified literals if the clause is not
	 *         simplified to true; null if the clause is simplified to true.
	 */
	public QuantLiteral[] getResultingQuantLits() {
		assert mResultingClauseTerm != null : "Quant: Substitution has not yet been performed.";
		return mResultingQuantLits;
	}

	/**
	 * After applying the substitution, get the resulting clause term.
	 * 
	 * @return the term representing the substituted clause. Note that it can be false or true.
	 */
	public Term getResultingClauseTerm() {
		assert mResultingClauseTerm != null : "Quant: Substitution has not yet been performed.";
		return mResultingClauseTerm;
	}

	/**
	 * Compute the result of applying a given variable substitution on a given quantified literal.
	 * 
	 * This method also normalizes and simplifies the resulting terms. The steps are:<br>
	 * (i) Substitute using FormulaUnLet ---> Proof rule for substitution.<br>
	 * (ii) Normalize using TermCompiler ---> Proof rule canonicalSum, cong, etc.<br>
	 * (iii) Simplify true and false lits.
	 * 
	 * TODO Proof production.
	 * 
	 * @return the term resulting from the substitution.
	 */
	private Term computeSubstitutedLiteralAsTerm(final QuantLiteral lit, final Map<TermVariable, Term> sigma) {
		assert !Collections.disjoint(Arrays.asList(lit.getTerm().getFreeVars()), sigma.keySet());

		final QuantLiteral atom = lit.getAtom();
		final Term term = atom.getTerm(); // TODO Quoted literals?

		// Substitute variables.
		final FormulaUnLet unletter = new FormulaUnLet();
		unletter.addSubstitutions(sigma);
		final Term substituted = unletter.transform(term);
		// TODO Proof production. Needs rule for substitution.

		// Normalize term.
		Term normalized = substituted;
		final TermCompiler compiler = mClausifier.getTermCompiler();
		final IProofTracker tracker = mClausifier.getTracker();

		if (atom instanceof QuantBoundConstraint) {
			// TODO store rewrite proof
			normalized = tracker.getProvedTerm(compiler.transform(substituted));
		} else { // Normalize lhs and rhs separately
			assert substituted instanceof ApplicationTerm;
			final ApplicationTerm subsEq = (ApplicationTerm) substituted;
			assert subsEq.getFunction().getName() == "=";
			final Term subsLhs = subsEq.getParameters()[0];
			final Term subsRhs = subsEq.getParameters()[1];

			if (subsLhs instanceof ApplicationTerm
					&& ((ApplicationTerm) subsLhs).getFunction().getName().startsWith("@AUX")) {
				assert subsRhs == mQuantTheory.getTheory().mTrue;
				final ApplicationTerm subsAuxTerm = (ApplicationTerm) subsLhs;
				final Term[] oldArgs = subsAuxTerm.getParameters();
				final Term[] normalizedArgs = new Term[oldArgs.length];
				for (int i = 0; i < oldArgs.length; i++) {
					normalizedArgs[i] = tracker.getProvedTerm(compiler.transform(oldArgs[i]));
				}
				final Term normalizedAuxTerm =
						mQuantTheory.getTheory().term(((ApplicationTerm) subsLhs).getFunction(), normalizedArgs);
				normalized = mQuantTheory.getTheory().term("=", normalizedAuxTerm, mQuantTheory.getTheory().mTrue);
			} else {
				final Term normalizedLhs = tracker.getProvedTerm(compiler.transform(subsLhs));
				final Term normalizedRhs = tracker.getProvedTerm(compiler.transform(subsRhs));
				normalized = mQuantTheory.getTheory().term("=", normalizedLhs, normalizedRhs);
			}
		}

		// TODO Proof production.

		// Simplify equality literals similar to EqualityProxy. (TermCompiler already takes care of <= literals).
		Term simplified = normalized;
		assert simplified instanceof ApplicationTerm;
		ApplicationTerm appTerm = (ApplicationTerm) simplified;
		if (appTerm.getFunction().getName() == "=") {
			final Term lhs = appTerm.getParameters()[0];
			final Term rhs = appTerm.getParameters()[1];
			final SMTAffineTerm diff = new SMTAffineTerm(lhs);
			diff.add(Rational.MONE, rhs);
			if (diff.isConstant()) {
				if (diff.getConstant().equals(Rational.ZERO)) {
					simplified = mQuantTheory.getTheory().mTrue;
				} else {
					simplified = mQuantTheory.getTheory().mFalse;
				}
			} else {
				diff.div(diff.getGcd());
				Sort sort = lhs.getSort();
				// Normalize equality to integer logic if all variables are integer.
				if (mQuantTheory.getTheory().getLogic().isIRA() && sort.getName().equals("Real")
						&& diff.isAllIntSummands()) {
					sort = mQuantTheory.getTheory().getSort("Int");
				}
				// Check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
				if (sort.getName().equals("Int") && !diff.getConstant().isIntegral()) {
					simplified = mQuantTheory.getTheory().mFalse;
				}
			}
		}
		// TODO Proof production.

		final Term result;
		if (lit.isNegated()) {
			result = mQuantTheory.getTheory().not(simplified);
			// TODO Proof production.
		} else {
			result = simplified;
		}
		return result;
	}
}
