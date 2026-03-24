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
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

/**
 * Collect a single literal to build a clause.
 *
 * @author Juergen Christ
 */
class CollectLiteral implements Operation {
	/**
	 *
	 */
	private final Clausifier mClausifier;
	private final Term mLiteral;
	private final BuildClause mClauseBuilder;

	public CollectLiteral(Clausifier clausifier, final Term term, final BuildClause collector) {
		mClausifier = clausifier;
		assert term.getSort() == term.getTheory().getBooleanSort();
		mLiteral = term;
		mClauseBuilder = collector;
	}

	private Term rewriteBooleanSubterms(final Term term, final SourceAnnotation source) {
		return new AuxCreator(source).transform(term);
	}

	@Override
	public void perform() {
		final Theory theory = mLiteral.getTheory();
		Term idx = mLiteral;
		boolean quantified = false;
		boolean positive = true;
		while (Clausifier.isNotTerm(idx)) {
			positive = !positive;
			idx = ((ApplicationTerm) idx).getParameters()[0];
		}
		if (idx instanceof ApplicationTerm) {
			if (mClausifier.mIsEprEnabled && EprTheory.isQuantifiedEprAtom(idx)) {
				// idx has implicitly forall-quantified variables
				// --> dont create a literal for the current term
				// (i.e. only the EPR-theory, not the DPLLEngine, will know it)
				final DPLLAtom eprAtom =
						mClausifier.getEprTheory().getEprAtom((ApplicationTerm) idx, 0, mClausifier.mStackLevel,
								mClauseBuilder.getSource());

				mClauseBuilder.addLiteral(positive ? eprAtom : eprAtom.negate(), idx, mClausifier.mTracker.reflexivity(idx),
						positive);
				return;
			}

			final ApplicationTerm at = (ApplicationTerm) idx;
			final ILiteral lit;
			if (mLiteral.mTmpCtr <= Config.OCC_INLINE_THRESHOLD
					&& (positive ? (at.getFunction() == theory.mOr || at.getFunction() == theory.mImplies)
							: at.getFunction() == theory.mAnd)) {
				final Annotation rule = at.getFunction() == theory.mOr ? ProofConstants.TAUT_OR_NEG
						: at.getFunction() == theory.mImplies ? ProofConstants.TAUT_IMP_NEG
								: ProofConstants.TAUT_AND_POS;
				final Term[] params = at.getParameters();
				final Term[] tautClause = new Term[params.length + 1];
				tautClause[0] = positive ? theory.term("not", idx) : idx;
				for (int i = 0; i < params.length; i++) {
					Term p = params[i];
					if (at.getFunction() == theory.mAnd
							|| (at.getFunction() == theory.mImplies && i < params.length - 1)) {
						p = theory.term("not", p);
					}
					tautClause[i + 1] = p;
				}
				final Term taut = mClausifier.mTracker.tautology(theory.term("or", tautClause), rule);
				mClauseBuilder.mCurrentLits.remove(mLiteral);
				mClauseBuilder.addResolution(taut, mLiteral);
				for (int i = params.length - 1; i >= 0; i--) {
					mClauseBuilder.collectLiteral(tautClause[i + 1]);
				}
				return;
			}

			if (idx.getFreeVars().length > 0) {
				quantified = true;
			}
			Term rewrite = mClausifier.mTracker.reflexivity(at);
			// TODO build a method for this, this part is used in several methods
			if (at.getFunction().getName().equals("true")) {
				lit = Clausifier.mTRUE;
			} else if (at.getFunction().getName().equals("false")) {
				lit = Clausifier.mFALSE;
			} else if (at.getFunction().getName().equals("=")) {
				assert at.getParameters()[0].getSort() != theory.getBooleanSort();
				final Term lhs = at.getParameters()[0];
				final Term rhs = at.getParameters()[1];

				if (quantified) {
					// Find trivially true or false QuantLiterals.
					final Term trivialEq = Clausifier.checkAndGetTrivialEquality(lhs, rhs, theory);
					if (trivialEq == theory.mTrue) {
						lit = Clausifier.mTRUE;
					} else if (trivialEq == theory.mFalse) {
						lit = Clausifier.mFALSE;
					} else {
						final Term newLhs = rewriteBooleanSubterms(lhs, mClauseBuilder.getSource());
						final Term newRhs = rewriteBooleanSubterms(rhs, mClauseBuilder.getSource());
						rewrite = mClausifier.mTracker.congruence(rewrite, new Term[] { newLhs, newRhs });
						lit = mClausifier.getQuantifierTheory().getQuantEquality(
								mClausifier.mTracker.getProvedTerm(newLhs),
								mClausifier.mTracker.getProvedTerm(newRhs), mClauseBuilder.getSource());
					}
				} else {
					final EqualityProxy eq = mClausifier.createEqualityProxy(lhs, rhs, mClauseBuilder.getSource());
					// eq == true and positive ==> set to true
					// eq == true and !positive ==> noop
					// eq == false and !positive ==> set to true
					// eq == false and positive ==> noop
					if (eq == EqualityProxy.getTrueProxy()) {
						lit = Clausifier.mTRUE;
					} else if (eq == EqualityProxy.getFalseProxy()) {
						lit = Clausifier.mFALSE;
					} else {
						lit = eq.getLiteral(mClauseBuilder.getSource());
					}
				}
			} else if (at.getFunction().getName().equals("<=")) {
				// (<= SMTAffineTerm 0)
				if (quantified) {
					final Term linTerm = at.getParameters()[0];
					final Term zero = at.getParameters()[1];
					final Term newLinTerm = rewriteBooleanSubterms(linTerm, mClauseBuilder.getSource());
					rewrite = mClausifier.mTracker.congruence(rewrite, new Term[] { newLinTerm, mClausifier.mTracker.reflexivity(zero) });
					lit = mClausifier.getQuantifierTheory().getQuantInequality(positive,
							mClausifier.mTracker.getProvedTerm(newLinTerm),
							mClauseBuilder.getSource());
				} else {
					lit = mClausifier.createLeq0(at, mClauseBuilder.getSource());
				}
			} else if (!at.getFunction().isInterpreted() || Clausifier.needCCTerm(at)) {
				if (quantified) {
					rewrite = rewriteBooleanSubterms(at, mClauseBuilder.getSource());
				}
				lit = mClausifier.createBooleanLit((ApplicationTerm) mClausifier.mTracker.getProvedTerm(rewrite),
						mClauseBuilder.getSource());
			} else {
				lit = mClausifier.createAnonLiteral(idx, mClauseBuilder.getSource());
				// aux axioms will always automatically created for quantified formulas
				if (idx.getFreeVars().length == 0) {
					if (positive) {
						mClausifier.addAuxAxioms(idx, true, mClauseBuilder.getSource());
					} else {
						mClausifier.addAuxAxioms(idx, false, mClauseBuilder.getSource());
					}
				}
			}
			// TODO end
			rewrite = mClausifier.mTracker.transitivity(rewrite,
					mClausifier.mTracker.intern(mClausifier.mTracker.getProvedTerm(rewrite), lit.getSMTFormula(theory)));
			mClauseBuilder.addLiteral(positive ? lit : lit.negate(), at, rewrite, positive);
		} else if (idx instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) idx;
			final Pair<Term, Annotation> converted = mClausifier.convertQuantifiedSubformula(positive, qf);
			final Term substituted = converted.getFirst();
			final Term lit = positive ? idx : theory.term(SMTLIBConstants.NOT, idx);
			final Term negLit = positive ? theory.term(SMTLIBConstants.NOT, idx) : idx;
			final Term tautology =
					mClausifier.mTracker.tautology(theory.term(SMTLIBConstants.OR, negLit, substituted), converted.getSecond());
			mClauseBuilder.mCurrentLits.remove(mLiteral);
			mClauseBuilder.addResolution(tautology, lit);
			final Term substitutedCanonic = mClausifier.mCompiler.transform(substituted);
			mClauseBuilder.addResolution(mClausifier.mTracker.rewriteToClause(substituted, substitutedCanonic), substituted);
			final Term newLiteral = mClausifier.mTracker.getProvedTerm(substitutedCanonic);
			mClauseBuilder.collectLiteral(newLiteral);
			return;
		} else if (idx instanceof TermVariable) {
			assert idx.getSort().equals(theory.getBooleanSort());
			// Build a quantified disequality, this allows us to use the literal for DER.
			// That is, x --> (x != false) and ~x --> (x != true),
			final Term value = positive ? theory.mFalse : theory.mTrue;
			final ILiteral lit = mClausifier.getQuantifierTheory().getQuantEquality(idx, value,
					mClauseBuilder.getSource());
			final Term rewrite = mClausifier.mTracker.intern(idx, (positive ? lit.negate() : lit).getSMTFormula(theory));
			mClauseBuilder.addLiteral(lit.negate(), idx, rewrite, positive);
		} else if (idx instanceof MatchTerm) {
			final ILiteral lit = mClausifier.createAnonLiteral(idx, mClauseBuilder.getSource());
			// aux axioms will always automatically created for quantified formulas
			if (idx.getFreeVars().length == 0) {
				if (positive) {
					mClausifier.addAuxAxioms(idx, true, mClauseBuilder.getSource());
				} else {
					mClausifier.addAuxAxioms(idx, false, mClauseBuilder.getSource());
				}
			}
			final Term rewrite = mClausifier.mTracker.intern(idx, lit.getSMTFormula(theory));
			mClauseBuilder.addLiteral(positive ? lit : lit.negate(), idx, rewrite, positive);
		} else {
			throw new SMTLIBException("Cannot handle literal " + mLiteral);
		}
	}

	@Override
	public String toString() {
		return "Collect" + mLiteral.toString();
	}

	class AuxCreator extends TermTransformer {

		private final SourceAnnotation mSource;

		public AuxCreator(final SourceAnnotation source) {
			mSource = source;
		}

		@Override
		public void convert(final Term term) {
			if (term.getSort().getName() == SMTLIBConstants.BOOL && shouldReplaceTerm(term)) {
				final Term auxTerm = mClausifier.createQuantAuxTerm(term, mSource);
				setResult(mClausifier.mTracker.buildRewrite(term, auxTerm, ProofConstants.RW_AUX_INTRO));
				return;
			}
			if (term instanceof ApplicationTerm) {
				super.convert(term);
			} else {
				setResult(mClausifier.mTracker.reflexivity(term));
				return;
			}
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			setResult(mClausifier.mTracker.congruence(mClausifier.mTracker.reflexivity(appTerm), newArgs));
		}

		boolean shouldReplaceTerm(final Term term) {
			return term.getFreeVars().length != 0 && !(term instanceof TermVariable)
					&& (!Clausifier.needCCTerm(term) || term instanceof QuantifiedFormula || term instanceof MatchTerm);
		}
	}
}