/*
 * Copyright (C) 2009-2012 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.OccurrenceCounter;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.NoopProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheorySettings;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LASharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.DestructiveEqualityReasoning.DERResult;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory.InstantiationMethod;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Utility to convert an arbitrary term into CNF and insert it into SMTInterpol.
 *
 * @author Juergen Christ, Jochen Hoenicke
 */
public class Clausifier {
	public class CCTermBuilder {
		private final SourceAnnotation mSource;

		private class BuildCCTerm implements Operation {
			private final Term mTerm;

			public BuildCCTerm(final Term term) {
				mTerm = term;
			}

			@Override
			public void perform() {
				CCTerm ccTerm = getCCTerm(mTerm);
				if (ccTerm != null) {
					mConverted.push(ccTerm);
				} else {
					if (needCCTerm(mTerm)) {
						final FunctionSymbol fs = ((ApplicationTerm) mTerm).getFunction();
						if (fs.isIntern() && fs.getName() == "select") {
							mArrayTheory.cleanCaches();
						}
						mOps.push(new SaveCCTerm(mTerm));
						final ApplicationTerm at = (ApplicationTerm) mTerm;
						final Term[] args = at.getParameters();
						for (int i = args.length - 1; i >= 0; --i) {
							mOps.push(new BuildCCAppTerm(i != args.length - 1));
							mOps.push(new BuildCCTerm(args[i]));
						}
						mConverted.push(mCClosure.getFuncTerm(fs));
					} else {
						// We have an intern function symbol
						ccTerm = mCClosure.createAnonTerm(mTerm);
						mCClosure.addTerm(ccTerm, mTerm);
						shareCCTerm(mTerm, ccTerm);
						addTermAxioms(mTerm, mSource);
						mConverted.push(ccTerm);
					}
				}
			}
		}

		private class SaveCCTerm implements Operation {
			private final Term mTerm;

			public SaveCCTerm(final Term term) {
				mTerm = term;
			}

			@Override
			public void perform() {
				final CCTerm ccTerm = mConverted.peek();
				mCClosure.addTerm(ccTerm, mTerm);
				shareCCTerm(mTerm, ccTerm);
				addTermAxioms(mTerm, mSource);
			}
		}

		/**
		 * Helper class to build the intermediate CCAppTerms. Note that all these terms will be func terms.
		 *
		 * @author Juergen Christ
		 */
		private class BuildCCAppTerm implements Operation {
			private final boolean mIsFunc;

			public BuildCCAppTerm(final boolean isFunc) {
				mIsFunc = isFunc;
			}

			@Override
			public void perform() {
				final CCTerm arg = mConverted.pop();
				final CCTerm func = mConverted.pop();
				mConverted.push(mCClosure.createAppTerm(mIsFunc, func, arg, mSource));
			}
		}

		private final ArrayDeque<Operation> mOps = new ArrayDeque<>();
		private final ArrayDeque<CCTerm> mConverted = new ArrayDeque<>();

		public CCTermBuilder(final SourceAnnotation source) {
			mSource = source;
		}

		public CCTerm convert(final Term t) {
			mOps.push(new BuildCCTerm(t));
			while (!mOps.isEmpty()) {
				mOps.pop().perform();
			}
			final CCTerm res = mConverted.pop();
			assert mConverted.isEmpty();
			return res;
		}
	}

	private interface Operation {
		public void perform();
	}

	private class AddAsAxiom implements Operation {
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
		 *            the term to assert annotated with its proof.
		 * @param source
		 *            the prepared proof node containing the source annotation.
		 */
		public AddAsAxiom(final Term axiom, final SourceAnnotation source) {
			assert axiom.getSort().getName() == "Bool";
			mAxiom = axiom;
			mSource = source;
		}

		@Override
		public void perform() {
			Term term = mTracker.getProvedTerm(mAxiom);
			boolean positive = true;
			if (isNotTerm(term)) {
				term = toPositive(term);
				positive = false;
			}
			final int oldFlags = getTermFlags(term);
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
			setTermFlags(term, oldFlags | assertedFlag);
			final ILiteral auxlit = getILiteral(term);
			if (auxlit != null) {
				// add the unit aux literal as clause; this will basically make the auxaxioms the axioms after unit
				// propagation and level 0 resolution.
				if ((oldFlags & auxFlag) == 0) {
					addAuxAxioms(term, positive, mSource);
				}
				buildClause(mAxiom, mSource);
				return;
			}
			final Theory t = mAxiom.getTheory();
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) term;
				if (at.getFunction() == t.mOr && !positive) {
					// the axioms added below already imply the auxaxiom clauses.
					setTermFlags(term, oldFlags | assertedFlag | auxFlag);
					// A negated or is an and of negated formulas. Hence assert all negated subformulas.
					for (final Term p : at.getParameters()) {
						final Term formula = t.term("not", p);
						final Term split =
								mTracker.modusPonens(mTracker.split(mAxiom, formula, ProofConstants.SPLIT_NEG_OR),
										mUtils.convertNot(mTracker.reflexivity(formula)));
						pushOperation(new AddAsAxiom(split, mSource));
					}
					return;
				} else if (at.getFunction().getName().equals("xor")
						&& at.getParameters()[0].getSort() == t.getBooleanSort()) {
					// the axioms added below already imply the auxaxiom clauses.
					setTermFlags(term, oldFlags | assertedFlag | auxFlag);
					final Term p1 = at.getParameters()[0];
					final Term p2 = at.getParameters()[1];
					if (positive) {
						// (xor p1 p2) --> (p1 \/ p2) /\ (~p1 \/ ~p2)
						Term formula = t.term("or", p1, p2);
						Term split = mTracker.split(mAxiom, formula, ProofConstants.SPLIT_POS_XOR_1);
						/* remove double negations; these may be in conflict with flatten */
						Term rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
						split = mTracker.modusPonens(split, rewrite);
						pushOperation(new AddAsAxiom(split, mSource));
						formula = t.term("or", t.term("not", p1), t.term("not", p2));
						split = mTracker.split(mAxiom, formula, ProofConstants.SPLIT_POS_XOR_2);
						/* remove double negations; these may be in conflict with flatten */
						rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
						split = mTracker.modusPonens(split, rewrite);
						pushOperation(new AddAsAxiom(split, mSource));
					} else {
						// (not (xor p1 p2)) --> (p1 \/ ~p2) /\ (~p1 \/ p2)
						Term formula = t.term("or", p1, t.term("not", p2));
						Term split = mTracker.split(mAxiom, formula, ProofConstants.SPLIT_NEG_XOR_1);
						pushOperation(new AddAsAxiom(split, mSource));
						formula = t.term("or", t.term("not", p1), p2);
						split = mTracker.split(mAxiom, formula, ProofConstants.SPLIT_NEG_XOR_2);
						/* remove double negations; these may be in conflict with flatten */
						final Term rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
						split = mTracker.modusPonens(split, rewrite);
						pushOperation(new AddAsAxiom(split, mSource));
					}
					return;
				} else if (at.getFunction().getName().equals("ite")) {
					// the axioms added below already imply the auxaxiom clauses.
					setTermFlags(term, oldFlags | assertedFlag | auxFlag);
					assert at.getFunction().getReturnSort() == t.getBooleanSort();
					final Term cond = at.getParameters()[0];
					Term thenForm = at.getParameters()[1];
					Term elseForm = at.getParameters()[2];
					Annotation kind1, kind2;
					if (positive) {
						kind1 = ProofConstants.SPLIT_POS_ITE_1;
						kind2 = ProofConstants.SPLIT_POS_ITE_2;
					} else {
						kind1 = ProofConstants.SPLIT_NEG_ITE_1;
						kind2 = ProofConstants.SPLIT_NEG_ITE_2;
						thenForm = t.term("not", thenForm);
						elseForm = t.term("not", elseForm);
					}
					Term formula = t.term("or", t.term("not", cond), thenForm);
					Term split = mTracker.split(mAxiom, formula, kind1);
					/* remove double negations; these may be in conflict with flatten */
					Term rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
					split = mTracker.modusPonens(split, rewrite);
					pushOperation(new AddAsAxiom(split, mSource));
					formula = t.term("or", cond, elseForm);
					split = mTracker.split(mAxiom, formula, kind2);
					/* remove double negations; these may be in conflict with flatten */
					rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
					split = mTracker.modusPonens(split, rewrite);
					pushOperation(new AddAsAxiom(split, mSource));
					return;
				}
			} else if (term instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) term;
				assert qf.getQuantifier() == QuantifiedFormula.EXISTS;
				final Pair<Term, Term[]> converted = convertQuantifiedSubformula(positive, qf);
				Term rewrite =
						positive ? mTracker.buildRewrite(mTracker.getProvedTerm(mAxiom), converted.getFirst(),
								ProofConstants.getRewriteSkolemAnnot(converted.getSecond()))
								: mTracker.buildRewrite(mTracker.getProvedTerm(mAxiom), converted.getFirst(),
										ProofConstants.getRewriteRemoveForallAnnot(converted.getSecond()));
				if (isNotTerm(converted.getFirst())) {
					rewrite = mUtils.convertNot(rewrite);
				}
				pushOperation(new AddAsAxiom(mTracker.modusPonens(mAxiom, rewrite), mSource));
				return;
			}
			buildClause(mAxiom, mSource);
		}
	}

	/**
	 * The ClauseCollector collects the literals for a clause. For every clause we build, we collect the literals in an
	 * underlying BuildClause object. There is also a ClauseCollector that collects the rewrite proof and adds the
	 * literals to the underlying BuildClause object.
	 *
	 * <p>
	 * If a clause contains a nested or, then a new clause collector is created. This collects the rewrite proof of the
	 * nested or. The corresponding literal is directly added to the main BuildClause object and the rewrite proof is
	 * stored and used to create the final rewrite proof of the nested or. When an or term is fully collected, it adds
	 * its own rewrite proof to the parent clause collector. We may in some cases also create new clause collectors for
	 * other terms.
	 *
	 * <p>
	 * The ClauseCollector is also an operation and runs when all its literals are collected. It creates the rewrite
	 * proof and add it to its parent.
	 *
	 * @author hoenicke
	 *
	 */
	private class ClauseCollector implements Operation {
		/**
		 * The object that collects the literals for this clause.
		 */
		private final BuildClause mClause;
		/**
		 * The parent collector for a nested or. This is null for the main collector of a clause. If this is not null,
		 * this is where the final rewrite proof is reported when this clause collector finishes.
		 */
		private final ClauseCollector mCollector;
		/**
		 * The first step of the rewrite proof that rewrites to the term that is collected in this clause.
		 */
		private final Term mRewriteProof;
		/**
		 * The array of sub rewrites, one for each subterm in a nested or term. The or term must be produced by
		 * mRewriteProof. If this array has length one, there is no nested or term and only one literal will be
		 * collected.
		 */
		private final Term[] mSubRewrites;
		/**
		 * The number of rewrites we have already written to the mSubRewrites array.
		 */
		private int mNumRewritesSeen;

		/**
		 * Create a new main clause collector for a clause. It collects the arguments of some term, usually
		 * clause.mClause, but it can also be rewritten to a simpler term before collecting it. If this is an or term
		 * than we collect each argument of the or separately and numArgs gives the number of arguments. Otherwise
		 * numArgs is one.
		 *
		 * @param clause
		 *            the clause where the literals are collected to.
		 * @param rewrite
		 *            The term we collect together with its rewrite proof from clause.mClause.
		 * @param numArgs
		 *            The number of arguments that should be collected.
		 */
		public ClauseCollector(final BuildClause clause, final Term rewrite, final int numArgs) {
			mClause = clause;
			mCollector = null;
			mRewriteProof = rewrite;
			mSubRewrites = new Term[numArgs];
		}

		/**
		 * Create a new sub clause collector under a parent clause collector. It acollects the arguments of some term,
		 * usually from the corresponding subterm in the parent literal. This term can have be rewritten to a simpler
		 * term before collecting it. If this is a nested or term than we collect each argument of the or separately and
		 * numArgs gives the number of arguments. Otherwise numArgs is one.
		 *
		 * @param parent
		 *            the parent clause collector, where we send our rewrite proof in the end.
		 * @param rewrite
		 *            The term we collect together with its rewrite proof from clause.mClause.
		 * @param numArgs
		 *            The number of arguments that should be collected.
		 */
		public ClauseCollector(final ClauseCollector parent, final Term rewrite, final int numArgs) {
			mClause = parent.getClause();
			mCollector = parent;
			mSubRewrites = new Term[numArgs];
			mRewriteProof = rewrite;
		}

		/**
		 * The underlying build clause object.
		 *
		 * @return the build clause object.
		 */
		public BuildClause getClause() {
			return mClause;
		}

		public SourceAnnotation getSource() {
			return mClause.getSource();
		}

		/**
		 * Add a rewrite proof without a literal. This is mainly used for nested or terms by the child collector. The
		 * child collector rewrites a nested or term to another nested or term for the final literals. Since the
		 * literals were already added, we only need to add the rewrite proof in that case.
		 *
		 * @param rewrite
		 *            the rewrite proof from the original argument to the literal.
		 */
		public void addRewrite(final Term rewrite) {
			assert rewrite != null;
			mSubRewrites[mNumRewritesSeen++] = rewrite;
		}

		/**
		 * Add a literal and its rewrite proof. This is called whenever we create a new literal. It is expected that
		 * every term rewrites to exactly one literal.
		 *
		 * @param lit
		 *            The collected literal.
		 * @param rewrite
		 *            the rewrite proof from the original argument to the literal.
		 */
		public void addLiteral(final ILiteral lit, final Term rewrite) {
			addRewrite(rewrite);
			mClause.addLiteral(lit);
		}

		@Override
		/**
		 * This performs the action of this clause collector after all literals have been collected. It computes the
		 * rewrite proof by combining the first step with all collected rewrites and adds the rewrite proof to the
		 * parent collector. If this is the top collector, it sends the rewrite proof to the BuildClause object to build
		 * the final clause.
		 */
		public void perform() {
			if (mClause.mIsTrue) {
				return;
			}
			assert mNumRewritesSeen == mSubRewrites.length;
			Term rewrite;
			if (mSubRewrites.length == 1) {
				rewrite = mTracker.transitivity(mRewriteProof, mSubRewrites[0]);
			} else {
				rewrite = mTracker.orMonotony(mRewriteProof, mSubRewrites);
				mClause.addFlatten(mTracker.getProvedTerm(rewrite));
			}

			if (mCollector == null) {
				mClause.buildClause(rewrite);
			} else {
				mCollector.addRewrite(rewrite);
			}
		}

		@Override
		public String toString() {
			return "CC" + mTracker.getProvedTerm(mRewriteProof);
		}
	}


	/**
	 * Collect a single literal to build a clause.
	 *
	 * @author Juergen Christ
	 */
	private class CollectLiteral implements Operation {
		private final Term mLiteral;
		private final ClauseCollector mCollector;

		public CollectLiteral(final Term term, final ClauseCollector collector) {
			assert term.getSort() == mTheory.getBooleanSort();
			mLiteral = term;
			mCollector = collector;
		}

		@Override
		public void perform() {
			final Theory theory = mLiteral.getTheory();
			Term rewrite = mTracker.reflexivity(mLiteral);
			if (isNotTerm(mLiteral)) {
				rewrite = mUtils.convertNot(rewrite);
			}
			Term idx = mTracker.getProvedTerm(rewrite);
			boolean positive = true;
			boolean quantified = false;
			if (isNotTerm(idx)) {
				idx = ((ApplicationTerm) idx).getParameters()[0];
				positive = false;
			}
			if (idx instanceof ApplicationTerm) {
				if (mIsEprEnabled && EprTheory.isQuantifiedEprAtom(idx)) {
					// idx has implicitly forall-quantified variables
					// --> dont create a literal for the current term
					// (i.e. only the EPR-theory, not the DPLLEngine, will know it)
					final DPLLAtom eprAtom =
							mEprTheory.getEprAtom((ApplicationTerm) idx, 0, mStackLevel, mCollector.getSource());

					mCollector.addLiteral(positive ? eprAtom : eprAtom.negate(), mLiteral);
					return;
				}

				final ApplicationTerm at = (ApplicationTerm) idx;
				ILiteral lit;
				Term atomRewrite = null;
				if (positive && at.getFunction() == theory.mOr && mLiteral.mTmpCtr <= Config.OCC_INLINE_THRESHOLD) {
					final Term[] params = at.getParameters();
					final ClauseCollector subCollector = new ClauseCollector(mCollector, rewrite, params.length);
					pushOperation(subCollector);
					for (int i = params.length - 1; i >= 0; i--) {
						pushOperation(new CollectLiteral(params[i], subCollector));
					}
					return;
				}

				if (idx.getFreeVars().length > 0) {
					quantified = true;
				}

				// TODO build a method for this, this part is used in several methods
				if (at.getFunction().getName().equals("true")) {
					lit = mTRUE;
				} else if (at.getFunction().getName().equals("false")) {
					lit = mFALSE;
				} else if (at.getFunction().getName().equals("=")) {
					assert at.getParameters()[0].getSort() != mTheory.getBooleanSort();
					final Term lhs = at.getParameters()[0];
					final Term rhs = at.getParameters()[1];

					if (quantified) {
						// Find trivially true or false QuantLiterals.
						final Term trivialEq = checkAndGetTrivialEquality(lhs, rhs, mTheory);
						if (trivialEq == mTheory.mTrue) {
							lit = mTRUE;
						} else if (trivialEq == mTheory.mFalse) {
							lit = mFALSE;
						} else {
							lit = mQuantTheory.getQuantEquality(lhs, rhs);
						}
					} else {
						final EqualityProxy eq = createEqualityProxy(lhs, rhs, mCollector.getSource());
						// eq == true and positive ==> set to true
						// eq == true and !positive ==> noop
						// eq == false and !positive ==> set to true
						// eq == false and positive ==> noop
						if (eq == EqualityProxy.getTrueProxy()) {
							lit = mTRUE;
						} else if (eq == EqualityProxy.getFalseProxy()) {
							lit = mFALSE;
						} else {
							lit = eq.getLiteral(mCollector.getSource());
						}
					}
				} else if (at.getFunction().getName().equals("<=")) {
					// (<= SMTAffineTerm 0)
					if (quantified) {
						final Term linTerm = at.getParameters()[0];
						lit = mQuantTheory.getQuantInequality(positive, linTerm);
					} else {
						lit = createLeq0(at, mCollector.getSource());
					}
				} else if (!at.getFunction().isInterpreted() || at.getFunction().getName().equals("select")) {
					lit = createBooleanLit(at, mCollector.getSource());
				} else {
					lit = createAnonLiteral(idx);
					if (positive) {
						addAuxAxioms(idx, true, mCollector.getSource());
					} else {
						addAuxAxioms(idx, false, mCollector.getSource());
					}
				}
				// TODO end

				atomRewrite = mTracker.intern(at, lit.getSMTFormula(theory, true));
				if (positive) {
					rewrite = mTracker.transitivity(rewrite, atomRewrite);
				} else {
					rewrite = mTracker.congruence(rewrite, new Term[] { atomRewrite });
					/* (not (<= -x 0)) can be rewritten to (not (not (< x 0))); remove double negation */
					rewrite = mUtils.convertNot(rewrite);
				}
				mCollector.addLiteral(positive ? lit : lit.negate(), rewrite);
			} else if (idx instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) idx;
				assert qf.getQuantifier() == QuantifiedFormula.EXISTS;
				final Pair<Term, Term[]> converted = convertQuantifiedSubformula(positive, qf);
				rewrite = mTracker.transitivity(rewrite,
						mTracker.buildRewrite(mTracker.getProvedTerm(rewrite), converted.getFirst(),
								positive ? ProofConstants.getRewriteSkolemAnnot(converted.getSecond())
										: ProofConstants.getRewriteRemoveForallAnnot(converted.getSecond())));
				if (isNotTerm(converted.getFirst())) {
					rewrite = mUtils.convertNot(rewrite);
				}
				final ClauseCollector subCollector = new ClauseCollector(mCollector, rewrite, 1);
				pushOperation(subCollector);
				pushOperation(new CollectLiteral(mTracker.getProvedTerm(rewrite), subCollector));
				return;
			} else if (idx instanceof TermVariable) {
				assert idx.getSort().equals(theory.getBooleanSort());
				// Build a quantified disequality, this allows us to use the literal for DER.
				// That is, x --> (x != false) and ~x --> (x != true),
				final Term value = positive ? mTheory.mFalse : mTheory.mTrue;
				final ILiteral lit = mQuantTheory.getQuantEquality(idx, value);
				final Term atomRewrite =
						mTracker.intern(idx, (positive ? lit.negate() : lit).getSMTFormula(theory, true));
				if (positive) {
					rewrite = mTracker.transitivity(rewrite, atomRewrite);
				} else {
					rewrite = mTracker.congruence(rewrite, new Term[] { atomRewrite });
				}
				mCollector.addLiteral(lit.negate(), rewrite);
			} else {
				throw new SMTLIBException("Cannot handle literal " + mLiteral);
			}
		}

		@Override
		public String toString() {
			return "Collect" + mLiteral.toString();
		}
	}

	/**
	 * Object to collect a clause and build it.
	 *
	 * @author Jürgen Christ, Jochen Hoenicke
	 */
	private class BuildClause {
		private boolean mIsTrue = false;
		private final LinkedHashSet<Literal> mLits = new LinkedHashSet<>();
		private final LinkedHashSet<QuantLiteral> mQuantLits = new LinkedHashSet<>();
		private final HashSet<Term> mFlattenedOrs = new HashSet<>();
		private final Term mClause;
		private boolean mSimpOr;
		private final SourceAnnotation mSource;

		public BuildClause(final Term clauseWithProof, final SourceAnnotation proofNode) {
			mClause = clauseWithProof;
			mSource = proofNode;
		}

		public SourceAnnotation getSource() {
			return mSource;
		}

		public void addFlatten(final Term term) {
			mFlattenedOrs.add(term);
		}

		/**
		 * Add a literal to the clause. This is called by the ClauseCollector for each literal that was added.
		 *
		 * @param lit
		 *            The literal to add to the clause.
		 */
		public void addLiteral(final ILiteral lit) {
			if (lit instanceof Literal) {
				assert ((Literal) lit).getAtom().getAssertionStackLevel() <= mEngine.getAssertionStackLevel();
			}
			if (lit == mTRUE) {
				mIsTrue = true;
			} else if (lit == mFALSE) {
				mSimpOr = true;
			} else if (lit instanceof Literal && mLits.add((Literal) lit)) {
				mIsTrue |= mLits.contains(((Literal) lit).negate());
			} else if (lit instanceof QuantLiteral && mQuantLits.add((QuantLiteral) lit)) {
				mIsTrue |= mQuantLits.contains(((QuantLiteral) lit).negate());
			} else {
				mSimpOr = true;
			}
		}

		/**
		 * Builds the final clause
		 *
		 * @param rewrite
		 *            the rewrite proof from mClause to a (possibly nested) or term with the final literals.
		 */
		public void buildClause(Term rewrite) {
			if (mIsTrue) {
				return;
			}
			// first finish the rewrite proof.
			// If this is zero, there is no or, if this is one there is only a top-level or that
			// doesn't have to be flattened.
			if (mFlattenedOrs.size() > 1) {
				// or needs to be flattened. mFlattenedOrs is the list of all flattened ors, including the top-level or.
				rewrite = mTracker.flatten(rewrite, mFlattenedOrs);
			}
			// simplify or, but only if we have seen false or duplicated literals and the term isn't already false
			if (mSimpOr && mTracker.getProvedTerm(rewrite) != rewrite.getTheory().mFalse) {
				rewrite = mTracker.orSimpClause(rewrite);
			}
			Term rewriteProof = mTracker.modusPonens(mClause, rewrite);
			Term proof = mTracker.getClauseProof(rewriteProof);
			boolean isDpllClause = true;

			final Literal[] lits = mLits.toArray(new Literal[mLits.size()]);
			final QuantLiteral[] quantLits = mQuantLits.toArray(new QuantLiteral[mQuantLits.size()]);
			if (mIsEprEnabled) {
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
				addClause(lits, null, getProofNewSource(proof, mSource));
			} else if (mIsEprEnabled) {
				// TODO: replace the nulls
				final Literal[] groundLiteralsAfterDER = mEprTheory.addEprClause(lits, null, null);

				if (groundLiteralsAfterDER != null) {
					addClause(groundLiteralsAfterDER, null, getProofNewSource(proof, mSource)); // TODO needs DER proof
				}
			} else {
				final DERResult resultFromDER =
						mQuantTheory.performDestructiveEqualityReasoning(rewriteProof, lits, quantLits, mSource);
				if (resultFromDER == null) {
					mQuantTheory.addQuantClause(lits, quantLits, mSource, rewriteProof);
				} else if (!resultFromDER.isTriviallyTrue()) { // Clauses that become trivially true can be dropped.
					isDpllClause = resultFromDER.isGround();
					// Build rewrite proof from all-intro, split-subst and derProof
					final TermVariable[] vars = mTracker.getProvedTerm(rewriteProof).getFreeVars();
					rewriteProof = mTracker.allIntro(rewriteProof, vars);
					final Annotation splitAnnot = ProofConstants.getSplitSubstAnnot(resultFromDER.getSubs());
					final Term splitProof = mTracker.split(rewriteProof, resultFromDER.getSubstituted(), splitAnnot);
					final Term derProof = resultFromDER.getSimplified();
					final Term rewriteProofAfterDER = mTracker.modusPonens(splitProof, derProof);

					if (isDpllClause) {
						addClause(resultFromDER.getGroundLits(), null,
								getProofNewSource(mTracker.getClauseProof(rewriteProofAfterDER), mSource));
					} else {
						mQuantTheory.addQuantClause(resultFromDER.getGroundLits(), resultFromDER.getQuantLits(),
								mSource, rewriteProofAfterDER);
					}
				}
			}
		}

		@Override
		public String toString() {
			return "BC" + mTracker.getProvedTerm(mClause);
		}
	}

	public static class ConditionChain implements Iterable<Term> {
		final ConditionChain mPrev;
		final Term mCond;
		final boolean mPositive;
		final int mSize;

		public ConditionChain() {
			mSize = 0;
			mPrev = null;
			mCond = null;
			mPositive = false;
		}

		public ConditionChain(final ConditionChain prev, final Term cond, final boolean positive) {
			mPrev = prev;
			mCond = cond;
			mPositive = positive;
			mSize = prev == null ? 1 : prev.mSize + 1;
		}

		public Term getTerm() {
			return mPositive ? mCond : mCond.getTheory().term("not", mCond);
		}

		public int size() {
			return mSize;
		}

		@Override
		public Iterator<Term> iterator() {
			return new Iterator<Term>() {
				ConditionChain walk = ConditionChain.this;

				@Override
				public boolean hasNext() {
					return walk.mSize > 0;
				}

				@Override
				public Term next() {
					final Term term = walk.getTerm();
					walk = walk.mPrev;
					return term;
				}
			};
		}

		public ConditionChain getPrevious() {
			return mPrev;
		}
	}

	private class AddTermITEAxiom implements Operation {

		private final SourceAnnotation mSource;

		private class CollectConditions implements Operation {
			private final ConditionChain mConds;
			private final Term mTerm;

			public CollectConditions(final ConditionChain conds, final Term term) {
				mConds = conds;
				mTerm = term;
			}

			@Override
			public void perform() {
				if (mTerm instanceof ApplicationTerm) {
					final ApplicationTerm at = (ApplicationTerm) mTerm;
					if (at.getFunction().getName().equals("ite")
							&& (at.mTmpCtr <= Config.OCC_INLINE_TERMITE_THRESHOLD || mConds.size() == 0)) {
						final Term c = at.getParameters()[0];
						final Term t = at.getParameters()[1];
						final Term e = at.getParameters()[2];
						pushOperation(new CollectConditions(new ConditionChain(mConds, c, false), t));
						pushOperation(new CollectConditions(new ConditionChain(mConds, c, true), e));
						return;
					}
				}
				// Not a nested ite term or a nested shared ite term
				final Theory theory = mTerm.getTheory();
				final Term[] literals = new Term[mConds.size() + 1];
				int offset = mConds.size();
				for (final Term cond : mConds) {
					literals[--offset] = cond;
				}
				literals[mConds.size()] = theory.term("=", mTermITE, mTerm);
				Term orTerm = theory.term("or", literals);
				Term axiom = mTracker.auxAxiom(orTerm, ProofConstants.AUX_TERM_ITE);

				/* remove double negations; these may be in conflict with flatten */
				final Term orRewrite = mUtils.convertFuncNot(mTracker.reflexivity(orTerm));
				axiom = mTracker.modusPonens(axiom, orRewrite);
				orTerm = mTracker.getProvedTerm(axiom);

				buildClause(axiom, mSource);
			}
		}

		private Term mMinValue = null;
		private Rational mMaxSubMin = null;
		private final Set<Term> visited = new HashSet<>();
		boolean mIsNotConstant = false;

		private class CheckBounds implements Operation {
			private final Term mTerm;

			public CheckBounds(final Term term) {
				mTerm = term;
			}

			@Override
			public void perform() {
				if (mIsNotConstant || !visited.add(mTerm)) {
					// already seen
					return;
				}
				if (mTerm instanceof ApplicationTerm) {
					final ApplicationTerm at = (ApplicationTerm) mTerm;
					if (at.getFunction().getName().equals("ite")) {
						final Term t = at.getParameters()[1];
						final Term e = at.getParameters()[2];
						pushOperation(new CheckBounds(t));
						pushOperation(new CheckBounds(e));
						return;
					}
				}
				// Not a nested ite term or a nested shared ite term
				// if this is the first term, just store it.
				if (mMinValue == null) {
					mMinValue = mTerm;
					mMaxSubMin = Rational.ZERO;
					return;
				}
				final SMTAffineTerm diff = new SMTAffineTerm(mMinValue);
				diff.negate();
				diff.add(new SMTAffineTerm(mTerm));
				if (!diff.isConstant()) {
					mIsNotConstant = true;
					return;
				}
				if (diff.getConstant().signum() < 0) {
					mMinValue = mTerm;
					mMaxSubMin = mMaxSubMin.sub(diff.getConstant());
				} else if (diff.getConstant().compareTo(mMaxSubMin) > 0) {
					mMaxSubMin = diff.getConstant();
				}
			}
		}

		private class AddBoundAxioms implements Operation {

			public AddBoundAxioms() {
			}

			@Override
			public void perform() {
				if (!mIsNotConstant && mMinValue != null) {
					// ite term is bounded by mMinValue and mMinValue + mMaxSubMin
					final Sort sort = mTermITE.getSort();
					final Theory theory = sort.getTheory();
					final Term zero = Rational.ZERO.toTerm(sort);
					final SMTAffineTerm diff = new SMTAffineTerm(mTermITE);
					diff.negate();
					diff.add(new SMTAffineTerm(mMinValue));
					final Term lboundAx = theory.term("<=", diff.toTerm(mCompiler, sort), zero);
					buildClause(mTracker.auxAxiom(lboundAx, ProofConstants.AUX_TERM_ITE_BOUND), mSource);
					diff.add(mMaxSubMin);
					diff.negate();
					final Term uboundAx = theory.term("<=", diff.toTerm(mCompiler, sort), zero);
					buildClause(mTracker.auxAxiom(uboundAx, ProofConstants.AUX_TERM_ITE_BOUND), mSource);
				}
			}
		}

		private final Term mTermITE;

		public AddTermITEAxiom(final Term termITE, final SourceAnnotation source) {
			mTermITE = termITE;
			mSource = source;
		}

		@Override
		public void perform() {
			pushOperation(new CollectConditions(new ConditionChain(), mTermITE));
			pushOperation(new AddBoundAxioms());
			pushOperation(new CheckBounds(mTermITE));
		}

	}

	/**
	 * Create a congruence closure term (CCTerm) for the given term. Also creates all necessary axioms for the term or
	 * sub-terms.
	 *
	 * @param term
	 *            The term for which a ccterm should be created.
	 * @param source
	 *            The source annotation that is used for auxiliary axioms.
	 * @return the ccterm.
	 */
	public CCTerm createCCTerm(final Term term, final SourceAnnotation source) {
		final CCTerm ccterm = new CCTermBuilder(source).convert(term);
		if (!mIsRunning) {
			run();
		}
		return ccterm;
	}

	public int getTermFlags(final Term term) {
		final Integer flags = mTermDataFlags.get(term);
		return flags == null ? 0 : (int) flags;
	}

	public void setTermFlags(final Term term, final int newFlags) {
		mTermDataFlags.put(term, newFlags);
	}

	public void share(final CCTerm ccTerm, final LASharedTerm laTerm) {
		getLASolver().addSharedTerm(laTerm);
		getCClosure().addSharedTerm(ccTerm);
	}

	public void shareLATerm(final Term term, final LASharedTerm laTerm) {
		assert !mLATerms.containsKey(term);
		mLATerms.put(term, laTerm);
		final CCTerm ccTerm = getCCTerm(term);
		if (ccTerm != null) {
			share(ccTerm, laTerm);
		}
	}

	public void shareCCTerm(final Term term, final CCTerm ccTerm) {
		assert !mCCTerms.containsKey(term);
		mCCTerms.put(term, ccTerm);
		final LASharedTerm laTerm = getLATerm(term);
		if (laTerm != null) {
			share(ccTerm, laTerm);
		}
	}

	public void addTermAxioms(final Term term, final SourceAnnotation source) {
		final int termFlags = getTermFlags(term);
		if ((termFlags & Clausifier.AUX_AXIOM_ADDED) == 0) {
			setTermFlags(term, termFlags | Clausifier.AUX_AXIOM_ADDED);
			if (term instanceof ApplicationTerm) {
				CCTerm ccTerm = getCCTerm(term);
				if (ccTerm == null && (needCCTerm(term) || term.getSort().isArraySort())) {
					final CCTermBuilder cc = new CCTermBuilder(source);
					ccTerm = cc.convert(term);
				}

				final ApplicationTerm at = (ApplicationTerm) term;
				final FunctionSymbol fs = at.getFunction();
				if (fs.isIntern()) {
					/* add axioms for certain built-in functions */
					if (fs.getName().equals("div")) {
						addDivideAxioms(at, source);
					} else if (fs.getName().equals("to_int")) {
						addToIntAxioms(at, source);
					} else if (fs.getName().equals("ite") && fs.getReturnSort() != mTheory.getBooleanSort()) {
						pushOperation(new AddTermITEAxiom(term, source));
					} else if (fs.getName().equals("store")) {
						addStoreAxiom(at, source);
					} else if (fs.getName().equals("@diff")) {
						addDiffAxiom(at, source);
						mArrayTheory.notifyDiff((CCAppTerm) ccTerm);
					}
				}

				if (term.getSort().isArraySort()) {
					assert ccTerm != null;
					final String funcName = at.getFunction().getName();
					final boolean isStore = funcName.equals("store");
					final boolean isConst = funcName.equals("const");
					mArrayTheory.notifyArray(getCCTerm(term), isStore, isConst);
				}
			}
			if (term.getSort().isNumericSort()) {
				boolean needsLA = term instanceof ConstantTerm;
				if (term instanceof ApplicationTerm) {
					final String func = ((ApplicationTerm) term).getFunction().getName();
					if (func.equals("+") || func.equals("-") || func.equals("*") || func.equals("to_real")) {
						needsLA = true;
					}
				}
				if (needsLA) {
					final MutableAffineTerm mat = createMutableAffinTerm(new SMTAffineTerm(term), source);
					assert mat.getConstant().mEps == 0;
					shareLATerm(term, new LASharedTerm(term, mat.getSummands(), mat.getConstant().mReal));
				}
			}
			if (term.getSort() == term.getTheory().getBooleanSort()) {
				/* If the term is a boolean term, add it's excluded middle axiom */
				if (term != term.getTheory().mTrue && term != term.getTheory().mFalse) {
					addExcludedMiddleAxiom(term, source);
				}
			}
		}
		if (!mIsRunning) {
			run();
		}
	}

	/**
	 * Get the (non-basic) linvar for a given term. The term must not be a constant or have arithmetic on the outside.
	 * The term must also be known to the linear solver.
	 *
	 * @param term
	 *            the SMT term.
	 * @return the linvar with linvar.getTerm() == term.
	 */
	public LinVar getLinVar(final Term term) {
		assert term.getSort().isNumericSort();
		assert term == SMTAffineTerm.create(term).getSummands().keySet().iterator().next();
		final LASharedTerm laShared = getLATerm(term);
		assert laShared != null;
		assert laShared.getSummands().size() == 1 && laShared.getOffset() == Rational.ZERO
				&& laShared.getSummands().values().iterator().next() == Rational.ONE;
		return laShared.getSummands().keySet().iterator().next();
	}

	/**
	 * Create a LinVar for a basic term. The term must be a non-basic (no arithmetic on the outside and not a constant)
	 * numeric term. This will create a linvar or return an already existing linvar.
	 *
	 * @param term
	 *            a non-basic term
	 * @param source
	 *            the source annotation, which is used to create auxiliary axioms for the term.
	 * @return the linvar with linvar.getTerm() == term.
	 */
	public LinVar createLinVar(final Term term, final SourceAnnotation source) {
		assert term.getSort().isNumericSort();
		assert term == SMTAffineTerm.create(term).getSummands().keySet().iterator().next();
		addTermAxioms(term, source);
		LASharedTerm laShared = getLATerm(term);
		if (laShared == null) {
			final boolean isint = term.getSort().getName().equals("Int");
			final LinVar lv = getLASolver().addVar(term, isint, getStackLevel());
			laShared = new LASharedTerm(term, Collections.singletonMap(lv, Rational.ONE), Rational.ZERO);
			shareLATerm(term, laShared);
		}
		assert laShared.getSummands().size() == 1 && laShared.getOffset() == Rational.ZERO
				&& laShared.getSummands().values().iterator().next() == Rational.ONE;
		return laShared.getSummands().keySet().iterator().next();
	}

	public MutableAffineTerm createMutableAffinTerm(final SMTAffineTerm at, final SourceAnnotation source) {
		final MutableAffineTerm res = new MutableAffineTerm();
		for (final Map.Entry<Term, Rational> summand : at.getSummands().entrySet()) {
			final LinVar lv = createLinVar(summand.getKey(), source);
			final Rational coeff = summand.getValue();
			res.add(coeff, lv);
		}
		res.add(at.getConstant());
		return res;
	}

	public CCTerm getCCTerm(final Term term) {
		return mCCTerms.get(term);
	}

	public LASharedTerm getLATerm(final Term term) {
		return mLATerms.get(term);
	}

	public ILiteral getILiteral(final Term term) {
		return mLiterals.get(term);
	}

	public void setLiteral(final Term term, final ILiteral lit) {
		mLiterals.put(term, lit);
	}

	public static boolean needCCTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fs = appTerm.getFunction();
			if (appTerm.getParameters().length == 0) {
				return false;
			}
			if (!fs.isIntern()) {
				return true;
			}
			if (fs.getName().startsWith("@AUX")) {
				return true;
			}
			switch (fs.getName()) {
			case "select":
			case "store":
			case "@diff":
			case "const":
			case "@EQ":
				return true;
			case "div":
			case "mod":
			case "/":
				return SMTAffineTerm.convertConstant((ConstantTerm) appTerm.getParameters()[1]) == Rational.ZERO;
			default:
				return false;
			}
		}
		return false;
	}

	/**
	 * A QuantifiedFormula is either skolemized or the universal quantifier is dropped before processing the subformula.
	 * 
	 * In the existential case, the variables are replaced by Skolem functions over the free variables. In the universal
	 * case, the variables are uniquely renamed.
	 *
	 * @param positive
	 * @param qf
	 * @return a pair of the resulting formula and the variable substitutions.
	 */
	private Pair<Term, Term[]> convertQuantifiedSubformula(final boolean positive, final QuantifiedFormula qf) {
		if (positive) {
			/*
			 * "exists" case
			 *
			 * skolemize everything inside, then go on as usual
			 */
			final TermVariable[] vars = qf.getVariables();
			final Term[] skolems = new Term[vars.length];
			for (int i = 0; i < vars.length; ++i) {
				skolems[i] = mTheory.skolemize(vars[i], qf);
			}

			if (mEprTheory != null) {
				mEprTheory.addSkolemConstants(skolems);
			}

			final FormulaUnLet unlet = new FormulaUnLet();
			unlet.addSubstitutions(new ArrayMap<>(vars, skolems));
			final Term skolemized = unlet.unlet(qf.getSubformula());
			return new Pair<>(skolemized, skolems);
		} else {
			/*
			 * "forall" case
			 *
			 * treatment of universally quantified subformulas: <li> alpha-rename quantified variables uniquely <li>
			 * drop the quantifier (remaining free TermVariables are implicitly universally quantified)
			 */

			final TermVariable[] vars = qf.getVariables();
			final Term[] freshVars = new Term[vars.length];
			for (int i = 0; i < vars.length; ++i) {
				freshVars[i] = mTheory.createFreshTermVariable(vars[i].getName(), vars[i].getSort());
			}

			final FormulaUnLet unlet = new FormulaUnLet();
			unlet.addSubstitutions(new ArrayMap<>(vars, freshVars));
			final Term uniquelyRenamed = unlet.unlet(qf.getSubformula());
			return new Pair<>(mTheory.term("not", uniquelyRenamed), freshVars);
		}
	}

	// flags for all interpreted or boolean terms
	public static final int AUX_AXIOM_ADDED = 16;
	public static final int NEG_AUX_AXIOMS_ADDED = 8;
	public static final int POS_AUX_AXIOMS_ADDED = 4;
	public static final int NEG_AXIOMS_ADDED = 2;
	public static final int POS_AXIOMS_ADDED = 1;

	/// Internalization stuff
	private final FormulaUnLet mUnlet = new FormulaUnLet();
	private final TermCompiler mCompiler = new TermCompiler();
	private final OccurrenceCounter mOccCounter = new OccurrenceCounter();
	private final Deque<Operation> mTodoStack = new ArrayDeque<>();

	private final Theory mTheory;
	private final DPLLEngine mEngine;
	private CClosure mCClosure;
	private LinArSolve mLASolver;
	private ArrayTheory mArrayTheory;
	private EprTheory mEprTheory;
	private QuantifierTheory mQuantTheory;

	/**
	 * True, if the run function is already active.
	 */
	private boolean mIsRunning = false;

	// TODO: make map or use option map
	private boolean mIsEprEnabled;
	private InstantiationMethod mInstantiationMethod;
	private boolean mIsUnknownTermDawgsEnabled;
	private boolean mPropagateUnknownTerms;
	private boolean mPropagateUnknownAux;

	/**
	 * Mapping from subformulas to their literal, if there was any created.
	 */
	private final ScopedHashMap<Term, ILiteral> mLiterals = new ScopedHashMap<>();
	/**
	 * Mapping from subterms to their CCTerm, if it was created.
	 */
	private final ScopedHashMap<Term, CCTerm> mCCTerms = new ScopedHashMap<>();
	/**
	 * Mapping from subterms to their LASharedTerm if it was created. This is always created for linear affine terms
	 * occuring under an uninterpreted function. It is also created for terms that appear as summand in some linear
	 * affine term.
	 */
	private final ScopedHashMap<Term, LASharedTerm> mLATerms = new ScopedHashMap<>();
	/**
	 * Mapping from subterms/subformulas to information about axioms and other information produced for these terms.
	 */
	private final ScopedHashMap<Term, Integer> mTermDataFlags = new ScopedHashMap<>();

	/**
	 * Keep all shared terms that need to be unshared from congruence closure when the top level is popped off the
	 * assertion stack.
	 */
	final ScopedArrayList<Term> mUnshareCC = new ScopedArrayList<>();
	/**
	 * Map of differences to equality proxies.
	 */
	final ScopedHashMap<SMTAffineTerm, EqualityProxy> mEqualities = new ScopedHashMap<>();
	/**
	 * Current assertion stack level.
	 */
	private int mStackLevel = 0;
	/**
	 * The number of pushes that failed since the solver already detected unsatisfiability.
	 */
	private int mNumFailedPushes = 0;
	/**
	 * Did we emit a warning on a failed push?
	 */
	private boolean mWarnedInconsistent = false;

	private final LogProxy mLogger;
	/**
	 * A tracker for proof production.
	 */
	private final IProofTracker mTracker;
	private final LogicSimplifier mUtils;

	final static ILiteral mTRUE = new TrueLiteral();
	final static ILiteral mFALSE = new FalseLiteral();

	public Clausifier(final Theory theory, final DPLLEngine engine, final int proofLevel) {
		mTheory = theory;
		mEngine = engine;
		mLogger = engine.getLogger();
		mTracker = proofLevel == 2 ? new ProofTracker() : new NoopProofTracker();
		mUtils = new LogicSimplifier(mTracker);
		mCompiler.setProofTracker(mTracker);
	}

	public void setAssignmentProduction(final boolean on) {
		mCompiler.setAssignmentProduction(on);
	}

	void pushOperation(final Operation op) {
		mTodoStack.push(op);
	}

	private static boolean isNotTerm(final Term t) {
		return (t instanceof ApplicationTerm) && ((ApplicationTerm) t).getFunction().getName() == "not";
	}

	/**
	 * Transform a term to a positive normal term. A term is a positive normal term if it
	 * <ul>
	 * <li>is an {@link ApplicationTerm} that does not correspond to a negation</li>
	 * <li>is a {@link QuantifiedFormula} that is existentially quantified</li>
	 * </ul>
	 *
	 * @param t
	 *            The term to compute the positive for.
	 * @return The positive of this term.
	 */
	private static Term toPositive(final Term t) {
		if (isNotTerm(t)) {
			return ((ApplicationTerm) t).getParameters()[0];
		}
		return t;
	}

	public void buildAuxClause(final ILiteral auxlit, final Term axiom, final SourceAnnotation source) {
		ApplicationTerm orTerm = (ApplicationTerm) mTracker.getProvedTerm(axiom);
		assert orTerm.getFunction().getName() == "or";
		assert orTerm.getParameters()[0] == auxlit.getSMTFormula(orTerm.getTheory(), true);

		/* first remove double negations; these may be in conflict with flatten */
		final Term orRewrite = mUtils.convertFuncNot(mTracker.reflexivity(orTerm));
		orTerm = (ApplicationTerm) mTracker.getProvedTerm(orRewrite);

		final BuildClause bc = new BuildClause(axiom, source);
		/* use the usual engine to create the other literals of the axiom. */
		final Term[] params = orTerm.getParameters();
		final ClauseCollector collector = new ClauseCollector(bc, orRewrite, params.length);
		pushOperation(collector);
		/* add auxlit directly to prevent it getting converted. No rewrite proof necessary */
		collector.addLiteral(auxlit, mTracker.reflexivity(auxlit.getSMTFormula(mTheory, true)));
		for (int i = params.length - 1; i >= 1; i--) {
			pushOperation(new CollectLiteral(params[i], collector));
		}
	}

	public void buildClause(final Term term, final SourceAnnotation source) {
		final BuildClause bc = new BuildClause(term, source);
		final Term rewrite = mTracker.reflexivity(mTracker.getProvedTerm(term));
		final ClauseCollector collector = new ClauseCollector(bc, rewrite, 1);
		pushOperation(collector);
		pushOperation(new CollectLiteral(mTracker.getProvedTerm(term), collector));
	}

	public void addAuxAxioms(final Term term, final boolean positive, final SourceAnnotation source) {
		assert term == toPositive(term);

		final int oldFlags = getTermFlags(term);
		final int auxflag = positive ? Clausifier.POS_AUX_AXIOMS_ADDED
				: Clausifier.NEG_AUX_AXIOMS_ADDED;
		if ((oldFlags & auxflag) != 0) {
			// We've already added the aux axioms
			// Nothing to do
			return;
		}
		setTermFlags(term, oldFlags | auxflag);

		final Theory t = term.getTheory();
		ILiteral negLit = getILiteral(term);
		assert negLit != null;
		negLit = positive ? negLit.negate() : negLit;
		final Term negLitTerm = negLit.getSMTFormula(t, true);
		if (term instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm) term;
			Term[] params = at.getParameters();
			if (at.getFunction() == t.mOr) {
				if (positive) {
					// (or (not (or t1 ... tn)) t1 ... tn)
					final Term[] literals = new Term[params.length + 1];
					literals[0] = negLitTerm;
					System.arraycopy(params, 0, literals, 1, params.length);
					final Term axiom = mTracker.auxAxiom(t.term("or", literals), ProofConstants.AUX_OR_POS);
					buildAuxClause(negLit, axiom, source);
				} else {
					// (or (or t1 ... tn)) (not ti))
					at = flattenOr(at);
					params = at.getParameters();
					for (final Term p : params) {
						final Term axiom = t.term("or", negLitTerm, t.term("not", p));
						final Term axiomProof = mTracker.auxAxiom(axiom, ProofConstants.AUX_OR_NEG);
						buildAuxClause(negLit, axiomProof, source);
					}
				}
			} else if (at.getFunction().getName().equals("ite")) {
				final Term cond = params[0];
				Term thenTerm = params[1];
				Term elseTerm = params[2];
				if (positive) {
					// (or (not (ite c t e)) (not c) t)
					// (or (not (ite c t e)) c e)
					// (or (not (ite c t e)) t e)
					Term axiom = t.term("or", negLitTerm, t.term("not", cond), thenTerm);
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_POS_1);
					buildAuxClause(negLit, axiom, source);
					axiom = t.term("or", negLitTerm, cond, elseTerm);
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_POS_2);
					buildAuxClause(negLit, axiom, source);
					if (Config.REDUNDANT_ITE_CLAUSES) {
						axiom = t.term("or", negLitTerm, thenTerm, elseTerm);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_POS_RED);
						buildAuxClause(negLit, axiom, source);
					}
				} else {
					// (or (ite c t e) (not c) (not t))
					// (or (ite c t e) c (not e))
					// (or (ite c t e) (not t) (not e))
					thenTerm = t.term("not", thenTerm);
					elseTerm = t.term("not", elseTerm);
					Term axiom = t.term("or", negLitTerm, t.term("not", cond), thenTerm);
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_NEG_1);
					buildAuxClause(negLit, axiom, source);
					axiom = t.term("or", negLitTerm, cond, elseTerm);
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_NEG_2);
					buildAuxClause(negLit, axiom, source);
					if (Config.REDUNDANT_ITE_CLAUSES) {
						axiom = t.term("or", negLitTerm, thenTerm, elseTerm);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_NEG_RED);
						buildAuxClause(negLit, axiom, source);
					}
				}
			} else if (at.getFunction().getName().equals("xor")) {
				assert at.getParameters().length == 2;
				final Term p1 = at.getParameters()[0];
				final Term p2 = at.getParameters()[1];
				// TODO We have the case x=t, and the boolean case as below.
				// Does the case below work for the boolean case with quantifiers?
				assert p1.getSort() == t.getBooleanSort();
				assert p2.getSort() == t.getBooleanSort();
				if (positive) {
					// (or (not (xor p1 p2)) p1 p2)
					// (or (not (xor p1 p2)) (not p1) (not p2))
					Term axiom = t.term("or", negLitTerm, p1, p2);
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_XOR_POS_1);
					buildAuxClause(negLit, axiom, source);
					axiom = t.term("or", negLitTerm, t.term("not", p1), t.term("not", p2));
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_XOR_POS_2);
					buildAuxClause(negLit, axiom, source);
				} else {
					// (or (xor p1 p2) p1 (not p2))
					// (or (xor p1 p2) (not p1) p2)
					Term axiom = t.term("or", negLitTerm, p1, t.term("not", p2));
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_XOR_NEG_1);
					buildAuxClause(negLit, axiom, source);
					axiom = t.term("or", negLitTerm, t.term("not", p1), p2);
					axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_XOR_NEG_2);
					buildAuxClause(negLit, axiom, source);
				}
			} else {
				throw new AssertionError("AuxAxiom not implemented: " + term);
			}
		} else {
			throw new AssertionError("Don't know how to create aux axiom: " + term);
		}
	}

	private ApplicationTerm flattenOr(final ApplicationTerm at) {
		final FunctionSymbol or = at.getFunction();
		assert or.getName().equals("or");
		final ArrayList<Term> flat = new ArrayList<>();
		final ArrayDeque<Term> todo = new ArrayDeque<>();
		todo.addAll(Arrays.asList(at.getParameters()));
		while (!todo.isEmpty()) {
			final Term first = todo.removeFirst();
			if (first instanceof ApplicationTerm) {
				final ApplicationTerm firstApp = (ApplicationTerm) first;
				if (firstApp.getFunction() == or && firstApp.mTmpCtr <= Config.OCC_INLINE_THRESHOLD) {
					final Term[] params = firstApp.getParameters();
					for (int i = params.length - 1; i >= 0; i--) {
						todo.addFirst(params[i]);
					}
					continue;
				}
			}
			flat.add(first);
		}
		return flat.size() == at.getParameters().length ? at
				: at.getTheory().term(or, flat.toArray(new Term[flat.size()]));
	}

	public void addStoreAxiom(final ApplicationTerm store, final SourceAnnotation source) {
		final Theory theory = store.getTheory();
		final Term i = store.getParameters()[1];
		final Term v = store.getParameters()[2];
		final Term axiom = theory.term("=", theory.term("select", store, i), v);

		final Term provedAxiom = mTracker.modusPonens(mTracker.auxAxiom(axiom, ProofConstants.AUX_ARRAY_STORE),
				mUtils.convertBinaryEq(mTracker.reflexivity(axiom)));
		buildClause(provedAxiom, source);
		if (Config.ARRAY_ALWAYS_ADD_READ
				// HACK: We mean "finite sorts"
				|| v.getSort() == mTheory.getBooleanSort()) {
			final Term a = store.getParameters()[0];
			final Term sel = mTheory.term("select", a, i);
			// Simply create the CCTerm
			createCCTerm(sel, source);
		}
	}

	public void addDiffAxiom(final ApplicationTerm diff, final SourceAnnotation source) {
		final Theory theory = diff.getTheory();
		// Create a = b \/ select(a, diff(a,b)) != select(b, diff(a,b))
		final Term a = diff.getParameters()[0];
		final Term b = diff.getParameters()[1];
		final Term axiom = theory.term("or", theory.term("=", a, b),
				theory.term("not", theory.term("=", theory.term("select", a, diff), theory.term("select", b, diff))));
		buildClause(mTracker.auxAxiom(axiom, ProofConstants.AUX_ARRAY_DIFF), source);
	}

	public void addDivideAxioms(final ApplicationTerm divTerm, final SourceAnnotation source) {
		final Theory theory = divTerm.getTheory();
		final Term[] divParams = divTerm.getParameters();
		final Rational divisor = (Rational) ((ConstantTerm) divParams[1]).getValue();
		if (divisor == Rational.ZERO) {
			/* Do not add any axiom if divisor is 0. */
			return;
		}
		final Term zero = Rational.ZERO.toTerm(divTerm.getSort());
		final SMTAffineTerm diff = new SMTAffineTerm(divParams[0]);
		diff.negate(); // -x
		diff.add(divisor, divTerm); // -x + d * (div x d)
		// (<= (+ (- x) (* d (div x d))) 0)
		Term axiom = theory.term("<=", diff.toTerm(mCompiler, divTerm.getSort()), zero);
		buildClause(mTracker.auxAxiom(axiom, ProofConstants.AUX_DIV_LOW), source);
		// (not (<= (+ (- x) (* d (div x d) |d|)) 0))
		diff.add(divisor.abs());
		axiom = theory.term("not", theory.term("<=", diff.toTerm(mCompiler, divTerm.getSort()), zero));
		buildClause(mTracker.auxAxiom(axiom, ProofConstants.AUX_DIV_HIGH), source);
	}

	/**
	 * Helper to add the auxiliary axioms for to_int axioms. Since the axioms for (to_int x) equal the axioms added for
	 * (div x 1), we reuse AddDivideAxioms.
	 */
	public void addToIntAxioms(final ApplicationTerm toIntTerm, final SourceAnnotation source) {
		final Theory theory = toIntTerm.getTheory();
		final Term realTerm = toIntTerm.getParameters()[0];
		final Term zero = Rational.ZERO.toTerm(realTerm.getSort());
		final SMTAffineTerm diff = new SMTAffineTerm(realTerm);
		diff.negate();
		diff.add(Rational.ONE, toIntTerm);
		// (<= (+ (to_real (to_int x)) (- x)) 0)
		Term axiom = theory.term("<=", diff.toTerm(mCompiler, realTerm.getSort()), zero);
		buildClause(mTracker.auxAxiom(axiom, ProofConstants.AUX_TO_INT_LOW), source);
		// (not (<= (+ (to_real (to_int x)) (- x) 1) 0))
		diff.add(Rational.ONE);
		axiom = theory.term("not", theory.term("<=", diff.toTerm(mCompiler, realTerm.getSort()), zero));
		buildClause(mTracker.auxAxiom(axiom, ProofConstants.AUX_TO_INT_HIGH), source);
	}

	/**
	 * Add the axioms for the law of excluded middle. This must happen if a Boolean function is used as a parameter to a
	 * non-Boolean function.
	 */
	public void addExcludedMiddleAxiom(final Term term, final SourceAnnotation source) {
		final Theory theory = term.getTheory();
		final EqualityProxy trueProxy = createEqualityProxy(term, theory.mTrue, source);
		final EqualityProxy falseProxy = createEqualityProxy(term, theory.mFalse, source);
		// These asserts should hold since we do not add excluded middle
		// axioms for true or false, and the equality proxies are
		// non-numeric
		assert trueProxy != EqualityProxy.getTrueProxy();
		assert trueProxy != EqualityProxy.getFalseProxy();
		assert falseProxy != EqualityProxy.getTrueProxy();
		assert falseProxy != EqualityProxy.getFalseProxy();

		final Literal trueLit = trueProxy.getLiteral(source);
		final Literal falseLit = falseProxy.getLiteral(source);

		// term => trueLit is trueLit \/ ~term
		Term axiom = theory.term("or", trueLit.getSMTFormula(theory, true), theory.term("not", term));
		axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_EXCLUDED_MIDDLE_1);
		buildAuxClause(trueLit, axiom, source);

		// ~term => falseLit is falseLit \/ term
		axiom = theory.term("or", falseLit.getSMTFormula(theory, true), term);
		axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_EXCLUDED_MIDDLE_2);
		buildAuxClause(falseLit, axiom, source);
	}

	/**
	 * Create an equality proxy for the terms lhs and rhs. This will check for trivial equality and return a false or
	 * true proxy instead. For others it creates the equality proxy. It also creates the terms and their term axioms for
	 * non-trivial equalities.
	 *
	 * @param lhs
	 *            the left-hand side of the equality
	 * @param rhs
	 *            the right-hand side of the equality.
	 * @param source
	 *            the source annotation used for term axioms. Use {@code null} to indicate that terms and their axioms
	 *            have already been created (used for N-O theory combination).
	 * @return the equality proxy.
	 */
	public EqualityProxy createEqualityProxy(final Term lhs, final Term rhs, final SourceAnnotation source) {
		final SMTAffineTerm diff = new SMTAffineTerm(lhs);
		diff.negate();
		diff.add(new SMTAffineTerm(rhs));
		if (diff.isConstant()) {
			if (diff.getConstant().equals(Rational.ZERO)) {
				return EqualityProxy.getTrueProxy();
			} else {
				return EqualityProxy.getFalseProxy();
			}
		}
		diff.div(diff.getGcd());
		Sort sort = lhs.getSort();
		// normalize equality to integer logic if all variables are integer.
		if (mTheory.getLogic().isIRA() && sort.getName().equals("Real") && diff.isAllIntSummands()) {
			sort = getTheory().getSort("Int");
		}
		// check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
		if (sort.getName().equals("Int") && !diff.getConstant().isIntegral()) {
			return EqualityProxy.getFalseProxy();
		}
		addTermAxioms(lhs, source);
		addTermAxioms(rhs, source);
		// we cannot really normalize the sign of the term. Try both signs.
		EqualityProxy eqForm = mEqualities.get(diff);
		if (eqForm != null) {
			return eqForm;
		}
		diff.negate();
		eqForm = mEqualities.get(diff);
		if (eqForm != null) {
			return eqForm;
		}
		eqForm = new EqualityProxy(this, lhs, rhs);
		mEqualities.put(diff, eqForm);
		return eqForm;
	}

	/**
	 * Check if an equality between two terms is trivially true or false.
	 * 
	 * @param lhs
	 *            the left side of the equality
	 * @param rhs
	 *            the right side of the equality
	 * @param theory
	 *            the theory
	 * @return the true (false) term if the equality is trivially true (false), null otherwise.
	 */
	public static Term checkAndGetTrivialEquality(final Term lhs, final Term rhs, final Theory theory) {
		// This code corresponds to the check in createEqualityProxy(...)
		final SMTAffineTerm diff = new SMTAffineTerm(lhs);
		diff.add(Rational.MONE, rhs);
		if (diff.isConstant()) {
			if (diff.getConstant().equals(Rational.ZERO)) {
				return theory.mTrue;
			} else {
				return theory.mFalse;
			}
		} else {
			diff.div(diff.getGcd());
			Sort sort = lhs.getSort();
			// Normalize equality to integer logic if all variables are integer.
			if (theory.getLogic().isIRA() && sort.getName().equals("Real") && diff.isAllIntSummands()) {
				sort = theory.getSort("Int");
			}
			// Check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
			if (sort.getName().equals("Int") && !diff.getConstant().isIntegral()) {
				return theory.mFalse;
			}
		}
		return null;
	}

	ILiteral createAnonLiteral(final Term term) {
		ILiteral lit = getILiteral(term);
		if (lit == null) {
			/*
			 * when inserting a cnf-auxvar (for tseitin-style encoding) in a quantified formula, we need it to depend on the
			 * currently active quantifiers
			 */
			if (term.getFreeVars().length > 0) {
				assert mTheory.getLogic().isQuantified() : "quantified variables in quantifier-free theory";
				final TermVariable[] freeVars = new TermVariable[term.getFreeVars().length];
				final Term[] freeVarsAsTerm = new Term[freeVars.length];
				for (int i = 0; i < freeVars.length; i++) {
					freeVars[i] = term.getFreeVars()[i];
					freeVarsAsTerm[i] = freeVars[i];
				}
				final FunctionSymbol fs = mTheory.createFreshAuxFunction(freeVars, term);
				final ApplicationTerm auxTerm = mTheory.term(fs, freeVarsAsTerm);
				if (mIsEprEnabled) {
					lit = mEprTheory.getEprAtom(auxTerm, 0, mStackLevel, SourceAnnotation.EMPTY_SOURCE_ANNOT);
				} else {
					// TODO Create CCBaseTerm for the aux func or pred (edit: this is done automatically when looking
					// for instantiation terms - should it be done earlier?)
					// We use an equality "f(x,y,...)=true", not a NamedAtom, as CClosure must treat the literal
					// instances.
					lit = mQuantTheory.getQuantEquality(auxTerm, mTheory.mTrue);
				}
			} else {
				lit = new NamedAtom(term, mStackLevel);
				mEngine.addAtom((NamedAtom) lit);
			}
			setLiteral(term, lit);
		}
		assert lit != null;
		return lit;
	}

	ILiteral getLiteralTseitin(final Term t, final SourceAnnotation source) {
		final Term idx = toPositive(t);
		final boolean pos = t == idx;
		final ILiteral lit = createAnonLiteral(idx);
		addAuxAxioms(idx, true, source);
		addAuxAxioms(idx, false, source);
		return pos ? lit : lit.negate();
	}

	void addClause(final Literal[] lits, final ClauseDeletionHook hook, final ProofNode proof) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Added Ground Clause: %s", Arrays.toString(lits));
		}

		// alex, late comment: don't do this here but in BuildClause.perform
		// /*
		// * Idea for EPR:
		// * - a clause that has a literal which has a quantified variable should not go into the Engine
		// * - the EPR theory should know the whole clause
		// * (the engine will set the non-quantified literals, but it "gets to know them" somewhere else (getLiteral or
		// so)
		// */

		// track which constants appear in ground clauses
		if (mEprTheory != null) {
			mEprTheory.addConstants(EprHelpers.collectAppearingConstants(lits, mTheory));
		}

		mEngine.addFormulaClause(lits, proof, hook);
	}

	void addUnshareCC(final Term shared) {
		mUnshareCC.add(shared);
	}

	private void setupCClosure() {
		if (mCClosure == null) {
			mCClosure = new CClosure(this);
			mEngine.addTheory(mCClosure);
			/*
			 * If we do not setup the cclosure at the root level, we remove it with the corresponding pop since the
			 * axiom true != false will be removed from the assertion stack as well.
			 */
			final SourceAnnotation source = SourceAnnotation.EMPTY_SOURCE_ANNOT;
			final Literal atom = createEqualityProxy(mTheory.mTrue, mTheory.mFalse, source).getLiteral(source);
			final Term trueEqFalse = mTheory.term("=", mTheory.mTrue, mTheory.mFalse);
			final Term axiom = mTracker.auxAxiom(mTheory.not(trueEqFalse), ProofConstants.AUX_TRUE_NOT_FALSE);
			final BuildClause bc = new BuildClause(axiom, source);
			final ClauseCollector collector = new ClauseCollector(bc, mTracker.reflexivity(mTracker.getProvedTerm(axiom)), 1);
			Term rewrite = mTracker.intern(trueEqFalse, atom.getSMTFormula(mTheory, true));
			rewrite = mTracker.congruence(mTracker.reflexivity(mTheory.not(trueEqFalse)), new Term[] { rewrite });
			collector.addLiteral(atom.negate(), rewrite);
			collector.perform();
		}
	}

	private void setupLinArithmetic() {
		if (mLASolver == null) {
			mLASolver = new LinArSolve(this);
			mEngine.addTheory(mLASolver);
		}
	}

	private void setupArrayTheory() {
		if (mArrayTheory == null) {
			mArrayTheory = new ArrayTheory(this, mCClosure);
			mEngine.addTheory(mArrayTheory);
		}
	}

	private void setupEprTheory() {
		// TODO maybe merge with setupQuantifiers, below?

		if (mEprTheory == null) {
			// mEprTheory = new EprTheory(this.getTheory());

			mEprTheory = new EprTheory(mTheory, mEngine, mCClosure, this);
			mEngine.addTheory(mEprTheory);
		}
	}

	private void setupQuantifiers() {
		if (mQuantTheory == null) {
			mQuantTheory =
					new QuantifierTheory(mTheory, mEngine, this, mInstantiationMethod, mIsUnknownTermDawgsEnabled,
							mPropagateUnknownTerms, mPropagateUnknownAux);
			mEngine.addTheory(mQuantTheory);
		}
	}

	public void setQuantifierOptions(final boolean isEprEnabled, final InstantiationMethod instMethod,
			final boolean enableUnknownTermDawgs, final boolean propagateUnknownTerm,
			final boolean propagateUnknownAux) {
		mIsEprEnabled = isEprEnabled;
		mInstantiationMethod = instMethod;
		mIsUnknownTermDawgsEnabled = enableUnknownTermDawgs;
		mPropagateUnknownTerms = propagateUnknownTerm;
		mPropagateUnknownAux = propagateUnknownAux;
	}

	public void setLogic(final Logics logic) {
		if (logic.isUF() || logic.isArray() || logic.isArithmetic() || logic.isQuantified()) {
			// also need UF for div/mod
			// and for quantifiers for AUX functions
			setupCClosure();
		}
		if (logic.isArithmetic()) {
			setupLinArithmetic();
		}
		if (logic.isArray()) {
			setupArrayTheory();
		}
		if (logic.isQuantified()) {
			// TODO How can we combine the two? For now, we keep EPR separately.
			if (mIsEprEnabled) {
				setupEprTheory();
			} else {
				setupQuantifiers();
			}
		}
	}

	// TODO What do we have to do for quantifiers here?
	public Iterable<BooleanVarAtom> getBooleanVars() {
		final Iterator<ILiteral> it = mLiterals.values().iterator();
		return () -> new Iterator<BooleanVarAtom>() {
			private BooleanVarAtom mNext = computeNext();

			private final BooleanVarAtom computeNext() {
				while (it.hasNext()) {
					final ILiteral lit = it.next();
					if (lit instanceof BooleanVarAtom) {
						return (BooleanVarAtom) lit;
					}
				}
				return null;
			}

			@Override
			public boolean hasNext() {
				return mNext != null;
			}

			@Override
			public BooleanVarAtom next() {
				final BooleanVarAtom res = mNext;
				if (res == null) {
					throw new NoSuchElementException();
				}
				mNext = computeNext();
				return res;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}

	private final void run() {
		try {
			mIsRunning = true;
			while (!mTodoStack.isEmpty()) {
				if (mEngine.isTerminationRequested()) {
					/* Note: Engine remembers incompleteness */
					return;
				}
				final Operation op = mTodoStack.pop();
				op.perform();
			}
		} finally {
			mTodoStack.clear();
			mIsRunning = false;
		}
	}

	public DPLLEngine getEngine() {
		return mEngine;
	}

	public CClosure getCClosure() {
		return mCClosure;
	}

	public LinArSolve getLASolver() {
		return mLASolver;
	}

	public LogProxy getLogger() {
		return mLogger;
	}

	public int getStackLevel() {
		return mStackLevel;
	}

	public void addFormula(final Term f) {
		assert mTodoStack.isEmpty();
		if (mEngine.inconsistent() && !mWarnedInconsistent) {
			mLogger.warn("Already inconsistent.");
			mWarnedInconsistent = true;
			return;
		}
		SourceAnnotation source = SourceAnnotation.EMPTY_SOURCE_ANNOT;
		if (mEngine.isProofGenerationEnabled()) {
			if (f instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) f;
				final Annotation[] annots = at.getAnnotations();
				for (final Annotation a : annots) {
					if (a.getKey().equals(":named")) {
						final String name = ((String) a.getValue()).intern();
						source = new SourceAnnotation(name, null);
						break;
					}
				}
			}
		}
		Term origFormula = mUnlet.unlet(f);
		Term simpFormula;
		try {
			simpFormula = mCompiler.transform(origFormula);
		} finally {
			mCompiler.reset();
		}
		simpFormula = mTracker.modusPonens(mTracker.asserted(origFormula), simpFormula);
		origFormula = null;

		mOccCounter.count(mTracker.getProvedTerm(simpFormula));
		final Map<Term, Set<String>> names = mCompiler.getNames();
		if (names != null) {
			for (final Map.Entry<Term, Set<String>> me : names.entrySet()) {
				trackAssignment(me.getKey(), me.getValue(), source);
			}
		}
		pushOperation(new AddAsAxiom(simpFormula, source));
		run();
		mOccCounter.reset(simpFormula);
		simpFormula = null;

		// logger.info("Added " + numClauses + " clauses, " + numAtoms
		// + " auxiliary atoms.");
	}

	public void push() {
		if (mEngine.inconsistent()) {
			if (!mWarnedInconsistent) {
				mLogger.info("Already inconsistent.");
				mWarnedInconsistent = true;
			}
			++mNumFailedPushes;
		} else {
			mEngine.push();
			++mStackLevel;
			mEqualities.beginScope();
			mTermDataFlags.beginScope();
			mLiterals.beginScope();
			mLATerms.beginScope();
			mCCTerms.beginScope();
		}
	}

	public void pop(int numpops) {
		if (numpops <= mNumFailedPushes) {
			mNumFailedPushes -= numpops;
			return;
		}
		mWarnedInconsistent = false;
		numpops -= mNumFailedPushes;
		mNumFailedPushes = 0;
		mEngine.pop(numpops);
		for (int i = 0; i < numpops; ++i) {
			mCCTerms.endScope();
			/* unshare all ccterms that are no longer shared with LA but were in the previous scope */
			for (final Term term : mLATerms.undoMap().keySet()) {
				final CCTerm ccTerm = getCCTerm(term);
				if (ccTerm != null) {
					ccTerm.unshare();
				}
			}
			mLATerms.endScope();
			mLiterals.endScope();
			mTermDataFlags.endScope();
			mEqualities.endScope();
		}
		mStackLevel -= numpops;
	}

	private ProofNode getProofNewSource(final Term proof, final SourceAnnotation source) {
		final SourceAnnotation annot = (proof == null ? source : new SourceAnnotation(source, proof));
		return new LeafNode(LeafNode.NO_THEORY, annot);
	}

	public Theory getTheory() {
		return mTheory;
	}

	/**
	 * This is called for named formulas and creates a literal for the whole term.
	 *
	 * @param term
	 * @param names
	 */
	private void trackAssignment(final Term term, final Set<String> names, final SourceAnnotation source) {
		ILiteral lit;
		final Term idx = toPositive(term);
		final boolean pos = idx == term;
		if (idx instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) idx;
			final FunctionSymbol fs = at.getFunction();
			if (fs.getName().equals("<=")) {
				lit = createLeq0(at, source);
			} else if (fs.getName().equals("=") && at.getParameters()[0].getSort() != mTheory.getBooleanSort()) {
				final EqualityProxy ep = createEqualityProxy(at.getParameters()[0], at.getParameters()[1], source);
				if (ep == EqualityProxy.getTrueProxy()) {
					lit = new DPLLAtom.TrueAtom();
				} else if (ep == EqualityProxy.getFalseProxy()) {
					lit = new DPLLAtom.TrueAtom().negate();
				} else {
					lit = ep.getLiteral(source);
				}
			} else if ((!fs.isIntern() || fs.getName().equals("select"))
					&& fs.getReturnSort() == mTheory.getBooleanSort()) {
				lit = createBooleanLit(at, source);
			} else if (at == mTheory.mTrue) {
				lit = new DPLLAtom.TrueAtom();
			} else if (at == mTheory.mFalse) {
				lit = new DPLLAtom.TrueAtom().negate();
			} else {
				lit = getLiteralTseitin(idx, source);
			}
		} else {
			lit = getLiteralTseitin(idx, source);
		}
		assert lit instanceof Literal;
		if (!pos) {
			lit = lit.negate();
		}
		for (final String name : names) {
			mEngine.trackAssignment(name, (Literal) lit);
		}
	}

	private Literal createLeq0(final ApplicationTerm leq0term, final SourceAnnotation source) {
		Literal lit = (Literal) getILiteral(leq0term);
		if (lit == null) {
			final SMTAffineTerm sum = new SMTAffineTerm(leq0term.getParameters()[0]);
			final MutableAffineTerm msum = createMutableAffinTerm(sum, source);
			lit = mLASolver.generateConstraint(msum, false);
			setLiteral(leq0term, lit);
			// we don't need to add any aux axioms for (<= t 0) literal.
			setTermFlags(leq0term, getTermFlags(leq0term) | Clausifier.POS_AUX_AXIOMS_ADDED
					| Clausifier.NEG_AUX_AXIOMS_ADDED);
		}
		return lit;
	}

	private ILiteral createBooleanLit(final ApplicationTerm term, final SourceAnnotation source) {
		ILiteral lit = getILiteral(term);
		if (lit == null) {
			if (term.getParameters().length == 0) {
				final DPLLAtom atom = new BooleanVarAtom(term, mStackLevel);
				mEngine.addAtom(atom);
				lit = atom;
			} else {
				if (term.getFreeVars().length > 0 && !mIsEprEnabled) {
					lit = mQuantTheory.getQuantEquality(term, mTheory.mTrue);

					// alex: this the right place to get rid of the CClosure predicate conversion in EPR-case?
					// --> seems to be one of three positions.. (keyword: predicate-to-function conversion)
				} else if ((mEprTheory != null && !EprTheorySettings.FullInstatiationMode)
						|| EprTheory.isQuantifiedEprAtom(term)) {
					// assuming right now that
					assert !term.getFunction().getName().equals("not") : "do something for the negated case!";

					// FIXME: how to tell getEprAtom which clause we are in????
					// TODO: replace 0 by hash value
					final EprAtom atom = mEprTheory.getEprAtom(term, 0, mStackLevel, source);
					lit = atom;
					// if (!atom.isQuantified)
					if (atom instanceof EprGroundPredicateAtom) {
						mEprTheory.addAtomToDPLLEngine(atom);
						// mEngine.addAtom(atom);
					}
				} else {
					// replace a predicate atom "(p x)" by "(p x) = true"
					final EqualityProxy eq = createEqualityProxy(term, mTheory.mTrue, source);
					// Safe since m_Term is neither true nor false
					assert eq != EqualityProxy.getTrueProxy();
					assert eq != EqualityProxy.getFalseProxy();
					lit = eq.getLiteral(source);

				}
			}
			setLiteral(term, lit);
			setTermFlags(term, getTermFlags(term) | Clausifier.POS_AUX_AXIOMS_ADDED
					| Clausifier.NEG_AUX_AXIOMS_ADDED);
		}
		return lit;
	}

	public IProofTracker getTracker() {
		return mTracker;
	}

	public LogicSimplifier getSimplifier() {
		return mUtils;
	}

	// TODO Do we need to change something here for quantifiers?
	// (For now, I added getGroundLit where a method returns a LiteralProxy.)
	public Literal getCreateLiteral(final Term f, final SourceAnnotation source) {
		Term tmp = mUnlet.unlet(f);
		Term tmp2;
		try {
			tmp2 = mCompiler.transform(tmp);
		} finally {
			mCompiler.reset();
		}
		tmp = null;
		mOccCounter.count(tmp2);

		ApplicationTerm at = (ApplicationTerm) mTracker.getProvedTerm(tmp2);
		boolean negated = false;
		FunctionSymbol fs = at.getFunction();
		if (fs == mTheory.mNot) {
			at = (ApplicationTerm) at.getParameters()[0];
			fs = at.getFunction();
			negated = true;
		}

		Literal res;
		if (!fs.isIntern() || fs.getName().equals("select")) {
			final ILiteral iLit = createBooleanLit(at, source);
			assert iLit instanceof Literal;
			res = (Literal) iLit;
		} else if (at == mTheory.mTrue) {
			res = new TrueAtom();
		} else if (at == mTheory.mFalse) {
			res = new TrueAtom().negate();
		} else if (fs.getName().equals("xor")) {
			final ILiteral iLit = getLiteralTseitin(at, source);
			assert iLit instanceof Literal;
			res = (Literal) iLit;
		} else if (fs.getName().equals("=")) {
			final EqualityProxy ep = createEqualityProxy(at.getParameters()[0], at.getParameters()[1], source);
			if (ep == EqualityProxy.getFalseProxy()) {
				res = new TrueAtom().negate();
			} else if (ep == EqualityProxy.getTrueProxy()) {
				res = new TrueAtom();
			} else {
				res = ep.getLiteral(source);
			}
		} else if (fs.getName().equals("<=")) {
			res = createLeq0(at, source);
		} else {
			final ILiteral iLit = getLiteralTseitin(at, source);
			assert iLit instanceof Literal;
			res = (Literal) iLit;
		}

		run();
		mOccCounter.reset(tmp2);
		tmp2 = null;
		return negated ? res.negate() : res;
	}

	public EprTheory getEprTheory() {
		return mEprTheory;
	}

	public QuantifierTheory getQuantifierTheory() {
		return mQuantTheory;
	}

	public TermCompiler getTermCompiler() {
		return mCompiler;
	}

	public static boolean shouldFlatten(final ApplicationTerm term) {
		return term.getFunction().getName() == "or" && term.mTmpCtr <= Config.OCC_INLINE_THRESHOLD;
	}

	private static class TrueLiteral implements ILiteral {
		@Override
		public ILiteral getAtom() {
			return this;
		}
		@Override
		public ILiteral negate() {
			return mFALSE;
		}
		@Override
		public boolean isGround() {
			return true;
		}
		@Override
		public Term getSMTFormula(final Theory theory, final boolean quoted) {
			return theory.mTrue;
		}
	}

	private static class FalseLiteral implements ILiteral {
		@Override
		public ILiteral getAtom() {
			return this;
		}
		@Override
		public ILiteral negate() {
			return mTRUE;
		}
		@Override
		public boolean isGround() {
			return true;
		}
		@Override
		public Term getSMTFormula(final Theory theory, final boolean quoted) {
			return theory.mFalse;
		}
	}
}
