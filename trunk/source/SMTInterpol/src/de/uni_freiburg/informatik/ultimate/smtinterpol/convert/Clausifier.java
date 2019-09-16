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
import java.util.Deque;
import java.util.HashMap;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;
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
				final SharedTerm shared = getSharedTerm(mTerm, true, mSource);
				if (shared.mCCterm == null) {
					final FunctionSymbol fs = getSymbol();
					if (fs == null) {
						// We have an intern function symbol
						final CCTerm res = mCClosure.createAnonTerm(shared);
						shared.setCCTerm(res);
						mConverted.push(res);
						if (mTerm.getSort().isArraySort()) {
							mArrayTheory.notifyArray(res, false, false);
						}
					} else {
						mOps.push(new SaveCCTerm(shared));
						final ApplicationTerm at = (ApplicationTerm) mTerm;
						final Term[] args = at.getParameters();
						for (int i = args.length - 1; i >= 0; --i) {
							mOps.push(new BuildCCAppTerm(i != args.length - 1));
							mOps.push(new BuildCCTerm(args[i]));
						}
						mConverted.push(mCClosure.getFuncTerm(fs));
					}
				} else {
					mConverted.push(shared.mCCterm);
				}
			}

			private FunctionSymbol getSymbol() {
				if (mTerm instanceof ApplicationTerm) {
					final ApplicationTerm at = (ApplicationTerm) mTerm;
					final FunctionSymbol fs = at.getFunction();
					// Don't descend into interpreted function symbols unless
					// it is a select or store
					if (Clausifier.needCCTerm(fs)) {
						return fs;
					}
				}
				return null;
			}
		}

		private class SaveCCTerm implements Operation {
			private final SharedTerm mShared;

			public SaveCCTerm(final SharedTerm shared) {
				mShared = shared;
			}

			@Override
			public void perform() {
				mShared.setCCTerm(mConverted.peek());
				mCClosure.addTerm(mShared.mCCterm, mShared);
				final Term t = mShared.getTerm();
				if (t.getSort().isArraySort()) {
					final ApplicationTerm at = (ApplicationTerm) t;
					final String funcName = at.getFunction().getName();
					mArrayTheory.notifyArray(mShared.mCCterm, funcName.equals("store"), funcName.equals("const"));
				}
				if (t instanceof ApplicationTerm && ((ApplicationTerm) t).getFunction().getName().equals("@diff")) {
					mArrayTheory.notifyDiff((CCAppTerm) mShared.mCCterm);
				}
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
				mConverted.push(mCClosure.createAppTerm(mIsFunc, func, arg));
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

	/**
	 * Basic interface used to undo certain events related to the assertion stack.
	 *
	 * Due to our instantiation mechanism, trail objects should only be used to undo changes related to push/pop and
	 * instantiations at the same time.
	 *
	 * @author Juergen Christ
	 */
	static abstract class TrailObject {
		private TrailObject mPrev;

		protected TrailObject() {
			mPrev = this;
		}

		protected TrailObject(final TrailObject prev) {
			mPrev = prev;
		}

		/**
		 * Undo an action performed since the corresponding push.
		 */
		public abstract void undo();

		public TrailObject getPrevious() {
			return mPrev;
		}

		void setPrevious(final TrailObject prev) {
			mPrev = prev;
		}

		/**
		 * Is this the end of the scope.
		 *
		 * @return <code>true</code> if this object represents the end of a scope.
		 */
		public boolean isScopeMarker() { // NOPMD
			return false;
		}
	}

	/**
	 * Mark the begin/end of a scope on the assertion stack.
	 *
	 * @author Juergen Christ
	 */
	private class ScopeMarker extends TrailObject {
		public ScopeMarker(final TrailObject prev) {
			super(prev);
		}

		@Override
		public void undo() {
			// Nothing to do here
		}

		@Override
		public boolean isScopeMarker() {
			return true;
		}
	}

	private class RemoveClausifierInfo extends TrailObject {
		private final Term mTerm;

		public RemoveClausifierInfo(final TrailObject prev, final Term term) {
			super(prev);
			mTerm = term;
		}

		@Override
		public void undo() {
			mClauseData.remove(mTerm);
		}
	}

	private class RemoveFlag extends TrailObject {
		private final ClausifierInfo mCi;
		private final int mFlag;

		public RemoveFlag(final TrailObject prev, final ClausifierInfo ci, final int flag) {
			super(prev);
			mCi = ci;
			mFlag = flag;
		}

		@Override
		public void undo() {
			mCi.clearFlag(mFlag);
		}
	}

	private class RemoveLiteral extends TrailObject {
		private final ClausifierInfo mCi;

		public RemoveLiteral(final TrailObject prev, final ClausifierInfo ci) {
			super(prev);
			mCi = ci;
		}

		@Override
		public void undo() {
			mCi.clearLiteral();
		}
	}

	private class RemoveAtom extends TrailObject {
		private final Term mTerm;

		public RemoveAtom(final TrailObject prev, final Term term) {
			super(prev);
			mTerm = term;
		}

		@Override
		public void undo() {
			mLiteralData.remove(mTerm);
		}
	}

	/**
	 * A helper class to remember whether a formula has been added as axioms or the corresponding aux axioms have been
	 * added. This info also contains a field to mark the aux axioms as blocked. We use this to prevent deletion of the
	 * aux axioms if the corresponding literal has been used to simplify clausification, i.e., we did not convert a
	 * top-level formula as axiom, but added the unit clause containing only the proxy literal. For quantifier-free
	 * logics, this feature is unused since we do not run into problems with the assertion stack management. If however
	 * a proxy was created as a result of a quantifier instantiation, the instantiation survives a push and an assertion
	 * on the next stacklevel triggers a simplification where we only use the proxy, we have to block all clauses
	 * defining the auxiliary literal. This will prevent the deletion of the quantifier instantiation which however is a
	 * top-level assertion now.
	 *
	 * @author Juergen Christ
	 */
	private static class ClausifierInfo {
		static final int POS_AXIOMS_ADDED = 1;
		static final int NEG_AXIOMS_ADDED = 2;
		static final int POS_AUX_AXIOMS_ADDED = 4;
		static final int NEG_AUX_AXIOMS_ADDED = 8;
		private ILiteral mLit;
		private int mFlags;

		public ClausifierInfo() {
			mLit = null;
			mFlags = 0;
		}

		public void setFlag(final int flag) {
			mFlags |= flag;
		}

		public void clearFlag(final int flag) {
			mFlags &= ~flag;
		}

		public boolean testFlags(final int flag) {
			return (mFlags & flag) != 0;
		}

		public ILiteral getLiteral() {
			return mLit;
		}

		public void setLiteral(final ILiteral lit) {
			mLit = lit;
		}

		public void clearLiteral() {
			mLit = null;
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
			final ClausifierInfo ci = getInfo(term);
			int flag, auxflag;
			if (positive) {
				flag = ClausifierInfo.POS_AXIOMS_ADDED;
				auxflag = ClausifierInfo.POS_AUX_AXIOMS_ADDED;
			} else {
				flag = ClausifierInfo.NEG_AXIOMS_ADDED;
				auxflag = ClausifierInfo.NEG_AUX_AXIOMS_ADDED;
			}
			if (ci.testFlags(flag)) {
				// We've already added this formula as axioms
				return;
			}
			ci.setFlag(flag);
			mUndoTrail = new RemoveFlag(mUndoTrail, ci, flag);
			final ILiteral auxlit = ci.getLiteral();
			if (auxlit != null) {
				// add the unit aux literal as clause; this will basically make the auxaxioms the axioms after unit
				// propagation and level 0 resolution.
				if (!ci.testFlags(auxflag)) {
					addAuxAxioms(term, positive, mSource);
				}
				buildClause(mAxiom, mSource);
				return;
			}
			final Theory t = mAxiom.getTheory();
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) term;
				if (at.getFunction() == t.mOr && !positive) {
					// these axioms already imply the auxaxiom clauses.
					ci.setFlag(auxflag);
					for (final Term p : at.getParameters()) {
						final Term formula = t.term("not", p);
						final Term split =
								mTracker.getRewriteProof(mTracker.split(mAxiom, formula, ProofConstants.SPLIT_NEG_OR),
										mUtils.convertNot(mTracker.reflexivity(formula)));
						pushOperation(new AddAsAxiom(split, mSource));
					}
					return;
				} else if (at.getFunction().getName().equals("xor")
						&& at.getParameters()[0].getSort() == t.getBooleanSort()) {
					// these axioms already imply the auxaxiom clauses.
					ci.setFlag(auxflag);
					final Term p1 = at.getParameters()[0];
					final Term p2 = at.getParameters()[1];
					if (positive) {
						// (xor p1 p2) --> (p1 \/ p2) /\ (~p1 \/ ~p2)
						Term formula = t.term("or", p1, p2);
						Term split = mTracker.split(mAxiom, formula, ProofConstants.SPLIT_POS_XOR_1);
						/* remove double negations; these may be in conflict with flatten */
						Term rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
						split = mTracker.getRewriteProof(split, rewrite);
						pushOperation(new AddAsAxiom(split, mSource));
						formula = t.term("or", t.term("not", p1), t.term("not", p2));
						split = mTracker.split(mAxiom, formula, ProofConstants.SPLIT_POS_XOR_2);
						/* remove double negations; these may be in conflict with flatten */
						rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
						split = mTracker.getRewriteProof(split, rewrite);
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
						split = mTracker.getRewriteProof(split, rewrite);
						pushOperation(new AddAsAxiom(split, mSource));
					}
					return;
				} else if (at.getFunction().getName().equals("ite")) {
					// these axioms already imply the auxaxiom clauses.
					ci.setFlag(auxflag);
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
					split = mTracker.getRewriteProof(split, rewrite);
					pushOperation(new AddAsAxiom(split, mSource));
					formula = t.term("or", cond, elseForm);
					split = mTracker.split(mAxiom, formula, kind2);
					/* remove double negations; these may be in conflict with flatten */
					rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
					split = mTracker.getRewriteProof(split, rewrite);
					pushOperation(new AddAsAxiom(split, mSource));
					return;
				}
			} else if (term instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) term;
				assert qf.getQuantifier() == QuantifiedFormula.EXISTS;
				final Term converted = convertQuantifiedSubformula(positive, qf);
				// FIXME: real proof rule?
				Term rewrite = mTracker.buildRewrite(mAxiom, converted, ProofConstants.RW_SORRY);
				if (isNotTerm(converted)) {
					rewrite = mUtils.convertNot(rewrite);
				}
				pushOperation(new AddAsAxiom(rewrite, mSource));
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
				rewrite = mTracker.congruence(mRewriteProof, mSubRewrites);
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

				if (at.getFunction().getName().equals("true")) {
					lit = mTRUE;
				} else if (at.getFunction().getName().equals("false")) {
					lit = mFALSE;
				} else if (at.getFunction().getName().equals("=")) {
					assert at.getParameters()[0].getSort() != mTheory.getBooleanSort();
					final Term lhs = at.getParameters()[0];
					final Term rhs = at.getParameters()[1];

					if (quantified) {
						// TODO Find trivially true or false QuantLiterals.
						lit = mQuantTheory.getQuantEquality(at, positive, mCollector.getSource(), lhs, rhs);
					} else {
						final SharedTerm slhs = getSharedTerm(lhs, mCollector.getSource());
						final SharedTerm srhs = getSharedTerm(rhs, mCollector.getSource());
						final EqualityProxy eq = createEqualityProxy(slhs, srhs);
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
						lit = mQuantTheory.getQuantInequality(at, positive, mCollector.getSource(), linTerm);
					} else {
						lit = createLeq0(at, mCollector.getSource());
					}
				} else if (!at.getFunction().isInterpreted() || at.getFunction().getName().equals("select")) {
					lit = createBooleanLit(at, mCollector.getSource());
				} else {
					lit = getLiteral(idx);
					if (positive) {
						addAuxAxioms(idx, true, mCollector.getSource());
					} else {
						addAuxAxioms(idx, false, mCollector.getSource());
					}
				}
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
				final Term converted = convertQuantifiedSubformula(positive, qf);
				// FIXME: real proof rule?
				rewrite = mTracker.buildRewrite(rewrite, converted, ProofConstants.RW_SORRY);
				if (isNotTerm(converted)) {
					rewrite = mUtils.convertNot(rewrite);
				}
				final ClauseCollector subCollector = new ClauseCollector(mCollector, rewrite, 1);
				pushOperation(subCollector);
				pushOperation(new CollectLiteral(mTracker.getProvedTerm(rewrite), subCollector));
				return;
			} else if (idx instanceof TermVariable) {
				// TODO Find trivially true or false QuantLiterals.
				Term value = positive ? mTheory.mFalse : mTheory.mTrue;
				Term equality = mTheory.equals(idx, value);
				ILiteral lit = mQuantTheory.getQuantEquality(equality, false, mCollector.getSource(), idx, value);
				Term atomRewrite = mTracker.intern(idx, positive ? mTheory.not(equality) : equality);
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
			Term proof = mTracker.getRewriteProof(mClause, rewrite);
			proof = mTracker.getClauseProof(proof);
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
					addClause(groundLiteralsAfterDER, null, getProofNewSource(proof, mSource));
				}
			} else {
				final ILiteral[] litsAfterDER =
						mQuantTheory.performDestructiveEqualityReasoning(lits, quantLits, mSource);
				if (litsAfterDER != null) { // Clauses that become trivially true can be dropped.

					// TODO Proof production.
					isDpllClause = true;
					for (ILiteral iLit : litsAfterDER) {
						if (iLit instanceof QuantLiteral) {
							isDpllClause = false;
						}
					}
					if (isDpllClause) {
						final Literal[] groundLits = new Literal[litsAfterDER.length];
						for (int i = 0; i < groundLits.length; i++) {
							groundLits[i] = (Literal) litsAfterDER[i];
						}
						addClause(groundLits, null, getProofNewSource(proof, mSource));
					} else {
						mQuantTheory.addQuantClause(litsAfterDER, mSource);
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
				literals[mConds.size()] = theory.term("=", mTermITE.getTerm(), mTerm);
				Term orTerm = theory.term("or", literals);
				Term axiom = mTracker.auxAxiom(orTerm, ProofConstants.AUX_TERM_ITE);

				/* remove double negations; these may be in conflict with flatten */
				final Term orRewrite = mUtils.convertFuncNot(mTracker.reflexivity(orTerm));
				axiom = mTracker.getRewriteProof(axiom, orRewrite);
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
					final SMTAffineTerm diff = new SMTAffineTerm(mTermITE.getTerm());
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

		private final SharedTerm mTermITE;

		public AddTermITEAxiom(final SharedTerm termITE, final SourceAnnotation source) {
			mTermITE = termITE;
			mSource = source;
		}

		@Override
		public void perform() {
			pushOperation(new CollectConditions(new ConditionChain(), mTermITE.getTerm()));
			pushOperation(new AddBoundAxioms());
			pushOperation(new CheckBounds(mTermITE.getTerm()));
		}

	}

	// Term creation
	public MutableAffineTerm createMutableAffinTerm(final SharedTerm term) {
		final MutableAffineTerm res = new MutableAffineTerm();
		term.shareWithLinAr();
		res.add(term.getFactor(), term.getLinVar());
		res.add(term.getOffset());
		return res;
	}

	public MutableAffineTerm createMutableAffinTerm(final SMTAffineTerm at, final SourceAnnotation source) {
		final MutableAffineTerm res = new MutableAffineTerm();
		res.add(at.getConstant());
		for (final Map.Entry<Term, Rational> summand : at.getSummands().entrySet()) {
			final SharedTerm shared = getSharedTerm(summand.getKey(), source);
			final Rational coeff = summand.getValue();
			shared.shareWithLinAr();
			res.add(shared.mFactor.mul(coeff), shared.getLinVar());
			res.add(shared.mOffset.mul(coeff));
		}
		return res;
	}

	/**
	 * Get or create a shared term for a term. This version also makes sure that all axioms (e.g. select-over-store) are
	 * added before a newly created shared term is returned.
	 */
	public SharedTerm getSharedTerm(final Term t, final SourceAnnotation source) {
		final SharedTerm shared = getSharedTerm(t, false, source);
		if (!mIsRunning) {
			run();
		}
		return shared;
	}

	/**
	 * Get or create a shared term for a term. This version does not force creation of a CCTerm for non-internal
	 * functions with arguments if <code>inCCTermBuilder</code> is <code>true</code>.
	 *
	 * As a side effect, this function adds divide, to_int, or ite axioms for the corresponding terms. Furthermore, For
	 * Boolean terms other than true or false the law of excluded middle is instantiated.
	 *
	 * @param t
	 *            The term to create a shared term for.
	 * @param inCCTermBuilder
	 *            Are we in {@link CCTermBuilder}?
	 * @return Shared term.
	 */
	public SharedTerm getSharedTerm(final Term t, final boolean inCCTermBuilder, final SourceAnnotation source) { // NOPMD
		SharedTerm res = mSharedTerms.get(t);
		if (res == null) {
			// if we reach here, t is neither true nor false
			res = new SharedTerm(this, t);
			mSharedTerms.put(t, res);
			if (t instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) t;
				// Special cases
				if (t.getSort() == t.getTheory().getBooleanSort() && inCCTermBuilder) {
					addExcludedMiddleAxiom(res, source);
				} else {
					final FunctionSymbol fs = at.getFunction();
					if (fs.isIntern()) {
						if (fs.getName().equals("div")) {
							addDivideAxioms(at, source);
						} else if (fs.getName().equals("to_int")) {
							addToIntAxioms(at, source);
						} else if (fs.getName().equals("ite") && fs.getReturnSort() != mTheory.getBooleanSort()) {
							pushOperation(new AddTermITEAxiom(res, source));
						} else if (fs.getName().equals("store")) {
							addStoreAxiom(at, source);
						} else if (fs.getName().equals("@diff")) {
							addDiffAxiom(at, source);
						}
					}
					if (needCCTerm(fs) && !inCCTermBuilder && at.getParameters().length > 0) {
						final CCTermBuilder cc = new CCTermBuilder(source);
						res.mCCterm = cc.convert(t);
					}
				}
			}
			if (t.getSort().isNumericSort()) {
				boolean needsLA = t instanceof ConstantTerm;
				if (t instanceof ApplicationTerm) {
					final String func = ((ApplicationTerm) t).getFunction().getName();
					if (func.equals("+") || func.equals("-") || func.equals("*") || func.equals("to_real")) {
						needsLA = true;
					}
				}
				if (needsLA) {
					getLASolver().generateSharedVar(res, createMutableAffinTerm(new SMTAffineTerm(t), source));
					addUnshareLA(res);
				}
			}
		}
		return res;
	}

	public static boolean needCCTerm(final FunctionSymbol fs) {
		// we also create CC function symbols for select/store/const. For const it is necessary, as the array theory
		// does not derive v = w --> (const v) = (const w). For select/store it makes congruence reason a bit simpler.
		return !fs.isInterpreted() || fs.getName() == "select" || fs.getName() == "store" || fs.getName() == "const";
	}

	/**
	 * A QuantifiedFormula is either skolemized or the universal quantifier is dropped before processing the subformula.
	 *
	 * @param positive
	 * @param qf
	 * @return
	 */
	private Term convertQuantifiedSubformula(final boolean positive, final QuantifiedFormula qf) {
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
			return skolemized;
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
			return mTheory.term("not", uniquelyRenamed);
		}
	}

	/// Internalization stuff
	private final FormulaUnLet mUnlet = new FormulaUnLet();
	private final TermCompiler mCompiler = new TermCompiler();
	private final OccurrenceCounter mOccCounter = new OccurrenceCounter();
	private final Deque<Operation> mTodoStack = new ArrayDeque<>();
	private int mAuxCounter = 0;

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

	private boolean mIsEprEnabled;

	/**
	 * Mapping from Boolean terms to information about clauses produced for these terms.
	 */
	private final Map<Term, ClausifierInfo> mClauseData = new HashMap<>();
	/**
	 * Mapping from Boolean base terms to literals. A term is considered a base term when it corresponds to an atom or
	 * its negation.
	 */
	private final Map<Term, ILiteral> mLiteralData = new HashMap<>();
	/**
	 * We cache the SharedTerms for true and false here to be able to quickly create excluded middle axioms.
	 */
	SharedTerm mSharedTrue, mSharedFalse;

	/// Assertion stack stuff
	/**
	 * The undo trail used as a stack.
	 */
	private TrailObject mUndoTrail = new TrailObject() {

		@Override
		public void undo() {
			// Nothing to do for this sentinel entry
		}
	};
	/**
	 * Keep all shared terms that need to be unshared from congruence closure when the top level is popped off the
	 * assertion stack.
	 */
	final ScopedArrayList<SharedTerm> mUnshareCC = new ScopedArrayList<>();
	/**
	 * Keep all shared terms that need to be unshared from linear arithmetic when the top level is popped off the
	 * assertion stack.
	 */
	final ScopedArrayList<SharedTerm> mUnshareLA = new ScopedArrayList<>();
	/**
	 * Mapping from terms to their corresponding shared terms.
	 */
	final ScopedHashMap<Term, SharedTerm> mSharedTerms = new ScopedHashMap<>();
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

	public Clausifier(final DPLLEngine engine, final int proofLevel) {
		mTheory = engine.getSMTTheory();
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

		final ClausifierInfo ci = getInfo(term);
		final int auxflag = positive ? ClausifierInfo.POS_AUX_AXIOMS_ADDED : ClausifierInfo.NEG_AUX_AXIOMS_ADDED;
		if (ci.testFlags(auxflag)) {
			// We've already added the aux axioms
			// Nothing to do
			return;
		}
		ci.setFlag(auxflag);
		mUndoTrail = new RemoveFlag(mUndoTrail, ci, auxflag);

		final Theory t = term.getTheory();
		ILiteral negLit = ci.getLiteral();
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

		final Term provedAxiom = mTracker.getRewriteProof(mTracker.auxAxiom(axiom, ProofConstants.AUX_ARRAY_STORE),
				mUtils.convertBinaryEq(mTracker.reflexivity(axiom)));
		buildClause(provedAxiom, source);
		if (Config.ARRAY_ALWAYS_ADD_READ
				// HACK: We mean "finite sorts"
				|| v.getSort() == mTheory.getBooleanSort()) {
			final Term a = store.getParameters()[0];
			final Term sel = mTheory.term("select", a, i);
			// Simply create the CCTerm
			getSharedTerm(sel, source);
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
	public void addExcludedMiddleAxiom(final SharedTerm shared, final SourceAnnotation source) {
		final EqualityProxy trueProxy = createEqualityProxy(shared, mSharedTrue);
		final EqualityProxy falseProxy = createEqualityProxy(shared, mSharedFalse);
		// These asserts should hold since we do not add excluded middle
		// axioms for true or false, and the equality proxies are
		// non-numeric
		assert trueProxy != EqualityProxy.getTrueProxy();
		assert trueProxy != EqualityProxy.getFalseProxy();
		assert falseProxy != EqualityProxy.getTrueProxy();
		assert falseProxy != EqualityProxy.getFalseProxy();

		final Term litTerm = shared.getTerm();
		final Theory theory = litTerm.getTheory();
		final ILiteral lit = createBooleanLit((ApplicationTerm) litTerm, source);
		final Literal trueLit = trueProxy.getLiteral(source);
		final Literal falseLit = falseProxy.getLiteral(source);
		final Term trueTerm = trueLit.getSMTFormula(theory);
		final Term falseTerm = falseLit.getSMTFormula(theory);
		// m_Term => thenForm is (not m_Term) \/ thenForm
		Term axiom = mTracker.auxAxiom(theory.term("or", theory.term("not", litTerm), trueTerm),
				ProofConstants.AUX_EXCLUDED_MIDDLE_1);
		BuildClause bc = new BuildClause(axiom, source);
		ClauseCollector collector = new ClauseCollector(bc, mTracker.reflexivity(mTracker.getProvedTerm(axiom)), 2);
		final Term litRewrite = mTracker.intern(litTerm, lit.getSMTFormula(theory, true));
		Term rewrite = mTracker.congruence(mTracker.reflexivity(mTheory.term("not", litTerm)),
				new Term[] { litRewrite });
		collector.addLiteral(lit.negate(), rewrite);
		rewrite = mTracker.intern(trueTerm, trueLit.getSMTFormula(theory, true));
		collector.addLiteral(trueLit, rewrite);
		collector.perform();
		// (not m_Term) => elseForm is m_Term \/ elseForm
		axiom = mTracker.auxAxiom(theory.term("or", litTerm, falseTerm), ProofConstants.AUX_EXCLUDED_MIDDLE_2);
		bc = new BuildClause(axiom, source);
		collector = new ClauseCollector(bc, mTracker.reflexivity(mTracker.getProvedTerm(axiom)), 2);
		collector.addLiteral(lit, litRewrite);
		rewrite = mTracker.intern(falseTerm, falseLit.getSMTFormula(theory, true));
		collector.addLiteral(falseLit, rewrite);
		collector.perform();
	}

	ILiteral createAnonAtom(final Term smtFormula) {
		ILiteral atom = null;
		/*
		 * when inserting a cnf-auxvar (for tseitin-style encoding) in a quantified formula, we need it to depend on the
		 * currently active quantifiers
		 */
		if (smtFormula.getFreeVars().length > 0) {
			assert mTheory.getLogic().isQuantified() : "quantified variables in quantifier-free theory";
			final TermVariable[] freeVars = new TermVariable[smtFormula.getFreeVars().length];
			final Term[] freeVarsAsTerm = new Term[freeVars.length];
			final Sort[] paramTypes = new Sort[freeVars.length];
			for (int i = 0; i < freeVars.length; i++) {
				freeVars[i] = smtFormula.getFreeVars()[i];
				freeVarsAsTerm[i] = freeVars[i];
				paramTypes[i] = freeVars[i].getSort();
			}
			final FunctionSymbol fs = mTheory.declareInternalFunction("@AUX" + (mAuxCounter++), paramTypes,
					freeVars, smtFormula, FunctionSymbol.UNINTERPRETEDINTERNAL); // TODO change flag in the future
			final ApplicationTerm auxTerm = mTheory.term(fs, freeVarsAsTerm);
			if (mIsEprEnabled) {
				atom = mEprTheory.getEprAtom(auxTerm, 0, mStackLevel, SourceAnnotation.EMPTY_SOURCE_ANNOT);
			} else {
				// TODO Create CCBaseTerm for the aux func or pred (edit: this is done automatically when looking
				// for instantiation terms - should it be done earlier?)
				// We use an equality "f(x,y,...)=true", not a NamedAtom, as CClosure must treat the literal instances.
				atom = mQuantTheory.getQuantEquality(auxTerm, true, null, auxTerm, mTheory.mTrue);
			}
		} else {
			atom = new NamedAtom(smtFormula, mStackLevel);
			mEngine.addAtom((NamedAtom) atom);
		}
		return atom;
	}

	BooleanVarAtom createBooleanVar(final Term smtFormula) {
		final BooleanVarAtom atom = new BooleanVarAtom(smtFormula, mStackLevel);
		mUndoTrail = new RemoveAtom(mUndoTrail, smtFormula);
		mEngine.addAtom(atom);
		return atom;
	}

	public EqualityProxy createEqualityProxy(final SharedTerm lhs, final SharedTerm rhs) {
		final SMTAffineTerm diff = new SMTAffineTerm(lhs.getTerm());
		diff.negate();
		diff.add(new SMTAffineTerm(rhs.getTerm()));
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

	ILiteral getLiteral(final Term idx) {
		ClausifierInfo ci = mClauseData.get(idx);
		if (ci == null) {
			ci = new ClausifierInfo();
			mClauseData.put(idx, ci);
			mUndoTrail = new RemoveClausifierInfo(mUndoTrail, idx);
		}
		if (ci.getLiteral() == null) {
			ci.setLiteral(createAnonAtom(idx));
			mUndoTrail = new RemoveLiteral(mUndoTrail, ci);
		}
		return ci.getLiteral();
	}

	ILiteral getLiteralTseitin(final Term t, final SourceAnnotation source) {
		final Term idx = toPositive(t);
		final boolean pos = t == idx;
		final ILiteral lit = getLiteral(idx);
		addAuxAxioms(idx, true, source);
		addAuxAxioms(idx, false, source);
		return pos ? lit : lit.negate();
	}

	ClausifierInfo getInfo(final Term idx) {
		assert idx == toPositive(idx);
		ClausifierInfo res = mClauseData.get(idx);
		if (res == null) {
			res = new ClausifierInfo();
			mClauseData.put(idx, res);
			mUndoTrail = new RemoveClausifierInfo(mUndoTrail, idx);
		}
		return res;
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

	void addToUndoTrail(final TrailObject obj) {
		obj.setPrevious(mUndoTrail);
		mUndoTrail = obj;
	}

	private void pushUndoTrail() {
		mUndoTrail = new ScopeMarker(mUndoTrail);
	}

	private void popUndoTrail() {
		while (!mUndoTrail.isScopeMarker()) {
			mUndoTrail.undo();
			mUndoTrail = mUndoTrail.getPrevious();
		}
		// Skip the scope marker
		mUndoTrail = mUndoTrail.getPrevious();
	}

	void addUnshareCC(final SharedTerm shared) {
		mUnshareCC.add(shared);
	}

	void addUnshareLA(final SharedTerm shared) {
		mUnshareLA.add(shared);
	}

	private void setupCClosure() {
		if (mCClosure == null) {
			mCClosure = new CClosure(mEngine);
			mEngine.addTheory(mCClosure);
			/*
			 * If we do not setup the cclosure at the root level, we remove it with the corresponding pop since the
			 * axiom true != false will be removed from the assertion stack as well.
			 */
			// we don't want to call getSharedTerm here, as this would create the excluded middle axioms.
			mSharedTrue = new SharedTerm(this, mTheory.mTrue);
			mSharedTrue.mCCterm = mCClosure.createAnonTerm(mSharedTrue);
			mSharedTerms.put(mTheory.mTrue, mSharedTrue);
			mSharedFalse = new SharedTerm(this, mTheory.mFalse);
			mSharedFalse.mCCterm = mCClosure.createAnonTerm(mSharedFalse);
			mSharedTerms.put(mTheory.mFalse, mSharedFalse);
			final SourceAnnotation source = SourceAnnotation.EMPTY_SOURCE_ANNOT;
			final Literal atom = createEqualityProxy(mSharedTrue, mSharedFalse).getLiteral(source);
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
			mLASolver = new LinArSolve(mEngine);
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
			mQuantTheory = new QuantifierTheory(mTheory, mEngine, this);
			mEngine.addTheory(mQuantTheory);
		}
	}

	public void setEPR(final boolean isEprEnabled) {
		mIsEprEnabled = isEprEnabled;
	}

	public void setLogic(final Logics logic) {
		if (logic.isUF() || logic.isArray() || logic.isArithmetic()) {
			// also need UF for div/mod
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
		return () -> new BooleanVarIterator(mLiteralData.values().iterator());
	}

	private static final class BooleanVarIterator implements Iterator<BooleanVarAtom> {
		private final Iterator<ILiteral> mIt;
		private BooleanVarAtom mNext;

		public BooleanVarIterator(final Iterator<ILiteral> it) {
			mIt = it;
			computeNext();
		}

		private final void computeNext() {
			while (mIt.hasNext()) {
				final ILiteral lit = mIt.next();
				if (lit != null && lit instanceof BooleanVarAtom) {
					mNext = (BooleanVarAtom) lit;
					return;
				}
			}
			mNext = null;
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
			computeNext();
			return res;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
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
		if (mEngine.inconsistent() && !mWarnedInconsistent) {
			mLogger.warn("Already inconsistent.");
			mWarnedInconsistent = true;
			return;
		}
		SourceAnnotation source = null;
		if (mEngine.isProofGenerationEnabled()) {
			source = SourceAnnotation.EMPTY_SOURCE_ANNOT;
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
		simpFormula = mTracker.getRewriteProof(mTracker.asserted(origFormula), simpFormula);
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
			mUnshareCC.beginScope();
			mUnshareLA.beginScope();
			mSharedTerms.beginScope();
			pushUndoTrail();
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
			for (final SharedTerm t : mUnshareCC.currentScope()) {
				t.unshareCC();
			}
			mUnshareCC.endScope();
			for (final SharedTerm t : mUnshareLA.currentScope()) {
				t.unshareLA();
			}
			mUnshareLA.endScope();
			mEqualities.endScope();
			popUndoTrail();
			mSharedTerms.endScope();
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
				final SharedTerm lhs = getSharedTerm(at.getParameters()[0], source);
				final SharedTerm rhs = getSharedTerm(at.getParameters()[1], source);
				final EqualityProxy ep = createEqualityProxy(lhs, rhs);
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
		ILiteral lit = mLiteralData.get(leq0term);
		if (lit != null) {
			assert lit instanceof Literal;
			return (Literal) lit;
		}
		final SMTAffineTerm sum = new SMTAffineTerm(leq0term.getParameters()[0]);
		final MutableAffineTerm msum = createMutableAffinTerm(sum, source);
		lit = mLASolver.generateConstraint(msum, false);
		assert lit instanceof Literal;
		mLiteralData.put(leq0term, lit);
		mUndoTrail = new RemoveAtom(mUndoTrail, leq0term);
		return (Literal) lit;
	}

	private ILiteral createBooleanLit(final ApplicationTerm term, final SourceAnnotation source) {
		ILiteral lit = mLiteralData.get(term);
			if (lit == null) {
				if (term.getParameters().length == 0) {
					lit = createBooleanVar(term);
				} else {
				if (term.getFreeVars().length > 0 && !mIsEprEnabled) {
					lit = mQuantTheory.getQuantEquality(term, true, source, term, term.getTheory().mTrue);

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
						final SharedTerm st = getSharedTerm(term, source);

						final EqualityProxy eq = createEqualityProxy(st, mSharedTrue);
						// Safe since m_Term is neither true nor false
						assert eq != EqualityProxy.getTrueProxy();
						assert eq != EqualityProxy.getFalseProxy();
						lit = eq.getLiteral(source);

					}
				}
				mLiteralData.put(term, lit);
			mUndoTrail = new RemoveAtom(mUndoTrail, term);
		}
		return lit;
	}

	public IProofTracker getTracker() {
		return mTracker;
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

		ApplicationTerm at = (ApplicationTerm) tmp2;
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
			final EqualityProxy ep = createEqualityProxy(getSharedTerm(at.getParameters()[0], source),
					getSharedTerm(at.getParameters()[1], source));
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
		public Term getSMTFormula(Theory theory, boolean quoted) {
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
		public Term getSMTFormula(Theory theory, boolean quoted) {
			return theory.mFalse;
		}
	}
}
