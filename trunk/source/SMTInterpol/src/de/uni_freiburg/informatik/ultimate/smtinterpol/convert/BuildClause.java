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

import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.DestructiveEqualityReasoning.DERResult;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;

/**
 * Object to collect a clause and build it.
 *
 * The BuildClause collects the literals for a clause and tracks the proof. For every clause we build, we collect
 * the literals in this object. It collects all resolution steps for all literal rewrites that are done internally.
 *
 * <p>
 * The BuildClause is also an operation and runs when all its literals are collected. It creates the clause and
 * annotates it with its resolution proof.
 *
 * @author hoenicke
 */
class BuildClause implements Operation {
	/**
	 *
	 */
	private final Clausifier mClausifier;
	/**
	 * The term that is collected into a clause. If the head symbol is not an or this denotes a unit clause. The
	 * unit clause "(or ...)" cannot be collected, but must be expanded by the caller.
	 */
	private final Term mClause;
	/**
	 * The array of sub rewrites, one for each subterm in a nested or term. The or term must be produced by
	 * mRewriteProof. If this array has length one, there is no nested or term and only one literal will be
	 * collected.
	 */
	private Term mProof;

	private boolean mIsTrue = false;
	final LinkedHashSet<Term> mCurrentLits = new LinkedHashSet<>();
	private final LinkedHashSet<Literal> mLits = new LinkedHashSet<>();
	private final LinkedHashSet<QuantLiteral> mQuantLits = new LinkedHashSet<>();
	private final SourceAnnotation mSource;

	public BuildClause(Clausifier clausifier, final Term clauseWithProof, final SourceAnnotation proofNode) {
		mClausifier = clausifier;
		mClause = clauseWithProof;
		mSource = proofNode;
		mProof = mClausifier.mTracker.getClauseProof(clauseWithProof);
	}

	public SourceAnnotation getSource() {
		return mSource;
	}

	/**
	 * Start collecting a term in a clause. This creates a literal collector for the literal, unless the literal was
	 * already collected.
	 *
	 * @param term
	 *            the disjunct to add to the clause.
	 */
	public void collectLiteral(Term term) {
		while (Clausifier.isNotTerm(term) && Clausifier.isNotTerm(((ApplicationTerm) term).getParameters()[0])) {
			final Term negated = ((ApplicationTerm) term).getParameters()[0];
			term = ((ApplicationTerm) negated).getParameters()[0];
		}
		if (mCurrentLits.add(term)) {
			mClausifier.pushOperation(new CollectLiteral(mClausifier, term, this));
		}
	}

	/**
	 * Add a literal to the clause. This is called by the ClauseCollector for each literal that was added.
	 *
	 * @param lit
	 *            The literal to add to the clause.
	 */
	public void addLiteral(final ILiteral lit) {
		if (lit instanceof Literal) {
			assert ((Literal) lit).getAtom().getAssertionStackLevel() <= mClausifier.getEngine()
					.getAssertionStackLevel();
		}
		if (lit == Clausifier.mTRUE) {
			mIsTrue = true;
		} else if (lit == Clausifier.mFALSE) {
			return;
		} else if (lit instanceof Literal) {
			if (mLits.add((Literal) lit)) {
				mIsTrue |= mLits.contains(((Literal) lit).negate());
			}
		} else if (lit instanceof QuantLiteral) {
			if (mQuantLits.add((QuantLiteral) lit)) {
				mIsTrue |= mQuantLits.contains(((QuantLiteral) lit).negate());
			}
		} else {
			throw new AssertionError("Unknown literal");
		}
	}

	/**
	 * Add a resolution step to the clause proof with an explicit literal.
	 *
	 * @param otherClause
	 *            the proof of the other antecedent
	 * @param pivotLit
	 *            the pivot literal as contained in the current clause.
	 */
	public void addResolution(final Term otherClause, final Term pivotLit) {
		if (mClausifier.mTracker instanceof ProofTracker && otherClause != null) {
			mProof = ((ProofTracker) mClausifier.mTracker).resolve(pivotLit, mProof, mClausifier.mTracker.getClauseProof(otherClause));
		}
	}

	/**
	 * Add a literal and its rewrite proof. This is called whenever we create a new literal. It is expected that
	 * every term rewrites to exactly one literal.
	 *
	 * @param lit
	 *            The collected literal.
	 * @param rewrite
	 *            the rewrite proof from the original argument to the literal.
	 * @param positive
	 *            True, if the literal occured positive in the original clause.
	 */
	public void addLiteral(final ILiteral lit, final Term origAtom, final Term rewriteAtom,
			final boolean positive) {
		final Theory theory = rewriteAtom.getTheory();
		final Term origLiteral = positive ? origAtom : theory.term(SMTLIBConstants.NOT, origAtom);
		final Term rewriteLiteral = positive ? rewriteAtom
				: mClausifier.mTracker.congruence(mClausifier.mTracker.reflexivity(origLiteral), new Term[] { rewriteAtom });
		assert mCurrentLits.contains(origLiteral);
		mCurrentLits.remove(origLiteral);
		addResolution(mClausifier.mTracker.rewriteToClause(origLiteral, rewriteLiteral), origLiteral);
		if (lit == Clausifier.mFALSE && mClausifier.mTracker instanceof ProofTracker) {
			/* resolve literal from clause */
			final Term trueFalseTerm = mClausifier.mTracker.getProvedTerm(rewriteAtom);
			assert positive ? trueFalseTerm == theory.mFalse : trueFalseTerm == theory.mTrue;
			final Term negTrueFalseTerm =
					positive ? theory.term(SMTLIBConstants.NOT, trueFalseTerm) : trueFalseTerm;
			final Annotation rule = positive ? ProofConstants.TAUT_FALSE_NEG : ProofConstants.TAUT_TRUE_POS;
			addResolution(mClausifier.mTracker.tautology(negTrueFalseTerm, rule), mClausifier.mTracker.getProvedTerm(rewriteLiteral));
		}
		addLiteral(lit);
	}

	/**
	 * For a quantified clause build the proof for the quantified formula from the proof of the clause with free
	 * variables.
	 *
	 * @param lits
	 *            the ground literals in the quantified formula.
	 * @param quantLits
	 *            the literals containing quantified variables in the quantified formula
	 * @param proof
	 *            the proof of the clause with free variabless.
	 * @return the proof for the unit clause containing the forall formula.
	 */
	private Term buildQuantifierProof(final Literal[] lits, final QuantLiteral[] quantLits) {
		final Theory theory = mClausifier.getTheory();
		final Term clause;
		if (lits.length + quantLits.length > 1) {
			final Term[] literals = new Term[lits.length + quantLits.length];
			int i = 0;
			for (final Literal l : lits) {
				literals[i++] = l.getSMTFormula(theory);
			}
			for (final QuantLiteral ql : quantLits) {
				literals[i++] = ql.getSMTFormula(theory);
			}
			clause = theory.term("or", literals);
			if (mClausifier.mTracker instanceof ProofTracker) {
				for (i = 0; i < literals.length; i++) {
					final Term orPos = mClausifier.mTracker.tautology(
							theory.term("or", clause, theory.term("not", literals[i])), ProofConstants.TAUT_OR_POS);
					addResolution(orPos, literals[i]);
				}
			}
		} else {
			assert lits.length == 0 && quantLits.length == 1 : "quantLits must not be empty";
			clause = quantLits[0].getSMTFormula(theory);
		}
		Term rewriteProof = theory.annotatedTerm(new Annotation[] { new Annotation(":proof", mProof) }, clause);
		rewriteProof = mClausifier.mTracker.allIntro(rewriteProof, clause.getFreeVars());
		return rewriteProof;
	}

	private ProofNode getProofNewSource(final Term proof, final SourceAnnotation source) {
		final SourceAnnotation annot = (proof == null ? source : new SourceAnnotation(source, proof));
		return new LeafNode(LeafNode.NO_THEORY, annot);
	}

	@Override
	/**
	 * This performs the action of this clause collector after all literals have been collected. It computes the
	 * rewrite proof by combining the first step with all collected rewrites and adds the rewrite proof to the
	 * parent collector. If this is the top collector, it sends the rewrite proof to the BuildClause object to build
	 * the final clause.
	 */
	public void perform() {
		if (mIsTrue) {
			return;
		}
		final Theory theory = mClause.getTheory();
		boolean isDpllClause = true;

		final Literal[] lits = mLits.toArray(new Literal[mLits.size()]);
		final QuantLiteral[] quantLits = mQuantLits.toArray(new QuantLiteral[mQuantLits.size()]);
		if (mClausifier.mIsEprEnabled) {
			for (final Literal l : lits) {
				if (l.getAtom() instanceof EprQuantifiedPredicateAtom
						|| l.getAtom() instanceof EprQuantifiedEqualityAtom) {
					// we have an EPR-clause
					isDpllClause = false;
					break;
				}
			}
		} else if (!mQuantLits.isEmpty()) {
			isDpllClause = false;
		}

		if (isDpllClause) {
			mClausifier.addClause(lits, null, getProofNewSource(mProof, mSource));
		} else if (mClausifier.mIsEprEnabled) {
			// TODO: replace the nulls
			final Literal[] groundLiteralsAfterDER = mClausifier.getEprTheory().addEprClause(lits, null, null);

			if (groundLiteralsAfterDER != null) {
				// TODO: needs DER proof
				mClausifier.addClause(groundLiteralsAfterDER, null, getProofNewSource(mProof, mSource));
			}
		} else {
			final QuantifierTheory quantTheory = mClausifier.getQuantifierTheory();
			final Term quantifierWithProof = buildQuantifierProof(lits, quantLits);
			TermVariable[] quantVars =
					((QuantifiedFormula) mClausifier.mTracker.getProvedTerm(quantifierWithProof)).getVariables();
			final DERResult resultFromDER =
					quantTheory.performDestructiveEqualityReasoning(quantVars, lits, quantLits, mSource);
			if (resultFromDER == null) {
				quantTheory.addQuantClause(quantVars, lits, quantLits, mSource, quantifierWithProof);
			} else if (!resultFromDER.isTriviallyTrue()) { // Clauses that become trivially true can be dropped.
				// Build rewrite proof from all-intro, split-subst and derProof
				final Annotation splitAnnot = ProofConstants.getTautForallNeg(resultFromDER.getSubs());
				final Term substituted = resultFromDER.getSubstituted();
				final Term splitProof =
						mClausifier.mTracker.resolveBinaryTautology(quantifierWithProof, substituted, splitAnnot);
				final Term derProof = resultFromDER.getSimplified();
				Term rewriteProofAfterDER = mClausifier.mTracker.modusPonens(splitProof, derProof);
				final Term provedAfterDER = mClausifier.mTracker.getProvedTerm(rewriteProofAfterDER);
				mProof = mClausifier.mTracker.getClauseProof(rewriteProofAfterDER);
				if (provedAfterDER instanceof ApplicationTerm) {
					final ApplicationTerm appTerm = (ApplicationTerm) provedAfterDER;
					if (appTerm.getFunction().getName().equals("or")) {
						final Term[] litsAfterDER = ((ApplicationTerm) provedAfterDER).getParameters();
						final Term[] orElimParam = new Term[litsAfterDER.length + 1];
						orElimParam[0] = theory.term("not", provedAfterDER);
						for (int i = 0; i < litsAfterDER.length; i++) {
							orElimParam[i + 1] = litsAfterDER[i];
						}
						final Term orElim =
								mClausifier.mTracker.tautology(theory.term("or", orElimParam), ProofConstants.TAUT_OR_NEG);
						addResolution(orElim, provedAfterDER);
					} else if (appTerm.getFunction().getName().equals("false")) {
						final Term pivot = theory.term("not", appTerm);
						final Term falseElim = mClausifier.mTracker.tautology(pivot, ProofConstants.TAUT_FALSE_NEG);
						addResolution(falseElim, provedAfterDER);
					}
				}
				final Literal[] derGroundLits = resultFromDER.getGroundLits();
				final QuantLiteral[] derQuantLits = resultFromDER.getQuantLits();
				if (derQuantLits.length == 0) {
					mClausifier.addClause(derGroundLits, null, getProofNewSource(mProof, mSource));
				} else {
					rewriteProofAfterDER = buildQuantifierProof(derGroundLits, derQuantLits);
					quantVars = ((QuantifiedFormula) mClausifier.mTracker.getProvedTerm(rewriteProofAfterDER)).getVariables();
					quantTheory.addQuantClause(quantVars, derGroundLits, derQuantLits, mSource,
							rewriteProofAfterDER);
				}
			}
		}
	}

	@Override
	public String toString() {
		return "BC" + mClausifier.mTracker.getProvedTerm(mClause);
	}
}