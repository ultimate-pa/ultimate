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
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
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

		private final ArrayDeque<Operation> mOps = new ArrayDeque<Operation>();
		private final ArrayDeque<CCTerm> mConverted = new ArrayDeque<CCTerm>();

		public CCTermBuilder(final SourceAnnotation source) {
			mSource = source;
			if (mCClosure == null) {
				// Delayed setup for @div0, @mod0, and @/0
				setupCClosure();
			}
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
	 * Helper class to remove a theory added at some higher scope level. This should be used with care. It's mainly
	 * intended to remove the cclosure that was added because of a @/0, @div0, or @mod0 function symbol in pure linear
	 * arithmetic.
	 *
	 * It is safe to do this as a trail object since we need a cclosure for all quantified theories.
	 *
	 * @author Juergen Christ
	 */
	private class RemoveTheory extends TrailObject {
		public RemoveTheory(final TrailObject prev) {
			super(prev);
		}

		@Override
		public void undo() {
			mEngine.removeTheory();
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
		private Literal mLit;
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

		public Literal getLiteral() {
			return mLit;
		}

		public void setLiteral(final Literal lit) {
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
		private final Term mTerm;
		/**
		 * The source node.
		 */
		private final SourceAnnotation mSource;

		/**
		 * Add the clauses for an asserted term.
		 *
		 * @param term
		 *            the term to assert annotated with its proof.
		 * @param source
		 *            the prepared proof node containing the source annotation.
		 */
		public AddAsAxiom(Term term, final SourceAnnotation source) {
			final Term axiom = mTracker.getProvedTerm(term);
			assert axiom.getSort().getName() == "Bool";
			if (isNotTerm(axiom)) {
				term = mTracker.getRewriteProof(term, mUtils.convertNot(mTracker.reflexivity(axiom)));
			}
			mTerm = term;
			mSource = source;
		}

		@Override
		public void perform() {
			Term term = mTracker.getProvedTerm(mTerm);
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
			final Literal auxlit = ci.getLiteral();
			if (auxlit != null) {
				// add the unit aux literal as clause; this will basically make the auxaxioms the axioms after unit
				// propagation and level 0 resolution.
				if (!ci.testFlags(auxflag)) {
					new AddAuxAxioms(term, positive, mSource).perform();
				}
				buildClause(mTerm, mSource);
				return;
			}
			final Theory t = mTerm.getTheory();
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) term;
				if (at.getFunction() == t.mOr && !positive) {
					// these axioms already imply the auxaxiom clauses.
					ci.setFlag(auxflag);
					for (final Term p : at.getParameters()) {
						final Term split = mTracker.split(t.term("not", p), mTerm, ProofConstants.SPLIT_NEG_OR);
						pushOperation(new AddAsAxiom(split, mSource));
					}
					return;
				} else if (at.getFunction().getName().equals("=")
						&& at.getParameters()[0].getSort() == t.getBooleanSort()) {
					// these axioms already imply the auxaxiom clauses.
					ci.setFlag(auxflag);
					final Term p1 = at.getParameters()[0];
					final Term p2 = at.getParameters()[1];
					if (positive) {
						// (= p1 p2) --> (p1 \/ ~p2) /\ (~p1 \/ p2)
						Term formula = t.term("or", p1, t.term("not", p2));
						Term split = mTracker.split(formula, mTerm, ProofConstants.SPLIT_POS_EQ_1);
						/* remove double negations; these may be in conflict with flatten */
						Term rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
						split = mTracker.getRewriteProof(split, rewrite);
						pushOperation(new AddAsAxiom(split, mSource));
						formula = t.term("or", t.term("not", p1), p2);
						split = mTracker.split(formula, mTerm, ProofConstants.SPLIT_POS_EQ_2);
						/* remove double negations; these may be in conflict with flatten */
						rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
						split = mTracker.getRewriteProof(split, rewrite);
						pushOperation(new AddAsAxiom(split, mSource));
					} else {
						// (= p1 p2) --> (p1 \/ ~p2) /\ (~p1 \/ p2)
						Term formula = t.term("or", p1, p2);
						Term split = mTracker.split(formula, mTerm, ProofConstants.SPLIT_NEG_EQ_1);
						pushOperation(new AddAsAxiom(split, mSource));
						formula = t.term("or", t.term("not", p1), t.term("not", p2));
						split = mTracker.split(formula, mTerm, ProofConstants.SPLIT_NEG_EQ_2);
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
					Term split = mTracker.split(formula, mTerm, kind1);
					/* remove double negations; these may be in conflict with flatten */
					Term rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
					split = mTracker.getRewriteProof(split, rewrite);
					pushOperation(new AddAsAxiom(split, mSource));
					formula = t.term("or", cond, elseForm);
					split = mTracker.split(formula, mTerm, kind2);
					/* remove double negations; these may be in conflict with flatten */
					rewrite = mUtils.convertFuncNot(mTracker.reflexivity(formula));
					split = mTracker.getRewriteProof(split, rewrite);
					pushOperation(new AddAsAxiom(split, mSource));
					return;
				}
			}
			buildClause(mTerm, mSource);
		}
	}

	private class AddAuxAxioms implements Operation {

		private final Term mTerm;
		private final boolean mPositive;
		private final SourceAnnotation mSource;

		public AddAuxAxioms(final Term term, final boolean pos, final SourceAnnotation source) {
			assert term == toPositive(term);
			mTerm = term;
			mPositive = pos;
			mSource = source;
		}

		@Override
		public void perform() {
			final ClausifierInfo ci = getInfo(mTerm);
			final int auxflag = mPositive ? ClausifierInfo.POS_AUX_AXIOMS_ADDED : ClausifierInfo.NEG_AUX_AXIOMS_ADDED;
			if (ci.testFlags(auxflag)) {
				// We've already added the aux axioms
				// Nothing to do
				return;
			}
			ci.setFlag(auxflag);
			mUndoTrail = new RemoveFlag(mUndoTrail, ci, auxflag);

			final Theory t = mTerm.getTheory();
			Literal negLit = ci.getLiteral();
			assert negLit != null;
			negLit = mPositive ? negLit.negate() : negLit;
			final Term negLitTerm = negLit.getSMTFormula(t, true);
			if (mTerm instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) mTerm;
				Term[] params = at.getParameters();
				if (at.getFunction() == t.mOr) {
					if (mPositive) {
						// (or (not (or t1 ... tn)) t1 ... tn)
						final Term[] literals = new Term[params.length + 1];
						literals[0] = negLitTerm;
						System.arraycopy(params, 0, literals, 1, params.length);
						final Term axiom = mTracker.auxAxiom(t.term("or", literals), ProofConstants.AUX_OR_POS);
						buildAuxClause(negLit, axiom, mSource);
					} else {
						// (or (or t1 ... tn)) (not ti))
						at = flattenOr(at);
						params = at.getParameters();
						for (final Term p : params) {
							final Term axiom = t.term("or", negLitTerm, t.term("not", p));
							final Term axiomProof = mTracker.auxAxiom(axiom, ProofConstants.AUX_OR_NEG);
							buildAuxClause(negLit, axiomProof, mSource);
						}
					}
				} else if (at.getFunction().getName().equals("ite")) {
					final Term cond = params[0];
					Term thenTerm = params[1];
					Term elseTerm = params[2];
					if (mPositive) {
						// (or (not (ite c t e)) (not c) t)
						// (or (not (ite c t e)) c e)
						// (or (not (ite c t e)) t e)
						Term axiom = t.term("or", negLitTerm, t.term("not", cond), thenTerm);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_POS_1);
						buildAuxClause(negLit, axiom, mSource);
						axiom = t.term("or", negLitTerm, cond, elseTerm);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_POS_2);
						buildAuxClause(negLit, axiom, mSource);
						if (Config.REDUNDANT_ITE_CLAUSES) {
							axiom = t.term("or", negLitTerm, thenTerm, elseTerm);
							axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_POS_RED);
							buildAuxClause(negLit, axiom, mSource);
						}
					} else {
						// (or (ite c t e) (not c) (not t))
						// (or (ite c t e) c (not e))
						// (or (ite c t e) (not t) (not e))
						thenTerm = t.term("not", thenTerm);
						elseTerm = t.term("not", elseTerm);
						Term axiom = t.term("or", negLitTerm, t.term("not", cond), thenTerm);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_NEG_1);
						buildAuxClause(negLit, axiom, mSource);
						axiom = t.term("or", negLitTerm, cond, elseTerm);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_NEG_2);
						buildAuxClause(negLit, axiom, mSource);
						if (Config.REDUNDANT_ITE_CLAUSES) {
							axiom = t.term("or", negLitTerm, thenTerm, elseTerm);
							axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_ITE_NEG_RED);
							buildAuxClause(negLit, axiom, mSource);
						}
					}
				} else if (at.getFunction().getName().equals("=")) {
					assert at.getParameters().length == 2;
					final Term p1 = at.getParameters()[0];
					final Term p2 = at.getParameters()[1];
					assert p1.getSort() == t.getBooleanSort();
					assert p2.getSort() == t.getBooleanSort();
					if (mPositive) {
						// (or (not (= p1 p2)) p1 (not p2))
						// (or (not (= p1 p2)) (not p1) p2)
						Term axiom = t.term("or", negLitTerm, p1, t.term("not", p2));
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_EQ_POS_1);
						buildAuxClause(negLit, axiom, mSource);
						axiom = t.term("or", negLitTerm, t.term("not", p1), p2);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_EQ_POS_2);
						buildAuxClause(negLit, axiom, mSource);
					} else {
						// (or (= p1 p2) p1 p2)
						// (or (= p1 p2) (not p1) (not p2))
						Term axiom = t.term("or", negLitTerm, p1, p2);
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_EQ_NEG_1);
						buildAuxClause(negLit, axiom, mSource);
						axiom = t.term("or", negLitTerm, t.term("not", p1), t.term("not", p2));
						axiom = mTracker.auxAxiom(axiom, ProofConstants.AUX_EQ_NEG_2);
						buildAuxClause(negLit, axiom, mSource);
					}
				} else {
					throw new InternalError("AuxAxiom not implemented: " + mTerm);
				}
			} else if (mTerm instanceof QuantifiedFormula) {
				// TODO: Correctly implement this once we support quantifiers.
				throw new SMTLIBException("Cannot create quantifier in quantifier-free logic");
			} else {
				throw new InternalError("Don't know how to create aux axiom: " + mTerm);
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
			return flat.size() == at.getParameters().length ? at :
					at.getTheory().term(or, flat.toArray(new Term[flat.size()]));
		}
	}

	/**
	 * Collect literals to build a clause.
	 *
	 * @author Juergen Christ
	 */
	private class CollectLiterals implements Operation {
		private final Term mTerm;
		private final BuildClause mCollector;

		public CollectLiterals(final Term term, final BuildClause collector) {
			assert term.getSort() == mTheory.getBooleanSort();
			mTerm = term;
			mCollector = collector;
		}

		@Override
		public void perform() {
			final Theory theory = mTerm.getTheory();
			Term rewrite = mTracker.reflexivity(mTerm);
			if (isNotTerm(mTerm)) {
				rewrite = mUtils.convertNot(rewrite);
			}
			Term idx = mTracker.getProvedTerm(rewrite);
			boolean positive = true;
			if (isNotTerm(idx)) {
				idx = ((ApplicationTerm) idx).getParameters()[0];
				positive = false;
			}
			if (mTerm == theory.mFalse) {
				mCollector.addRewrite(rewrite);
				mCollector.setSimpOr();
				return;
			}
			if (mTerm == theory.mTrue) {
				mCollector.setTrue();
				return;
			}
			if (idx instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) idx;
				Literal atom;
				Term atomRewrite = null;
				if (positive && at.getFunction() == theory.mOr && mTerm.mTmpCtr <= Config.OCC_INLINE_THRESHOLD) {
					mCollector.addFlatten(at);
					final Term[] params = at.getParameters();
					for (int i = params.length - 1; i >= 0; i--) {
						pushOperation(new CollectLiterals(params[i], mCollector));
					}
					return;
				} else if (at.getFunction().getName().equals("=")
						&& at.getParameters()[0].getSort() != mTheory.getBooleanSort()) {
					final Term lhs = at.getParameters()[0];
					final Term rhs = at.getParameters()[1];
					final SharedTerm slhs = getSharedTerm(lhs, mCollector.mSource);
					final SharedTerm srhs = getSharedTerm(rhs, mCollector.mSource);
					final EqualityProxy eq = createEqualityProxy(slhs, srhs);
					// eq == true and positive ==> set to true
					// eq == true and !positive ==> noop
					// eq == false and !positive ==> set to true
					// eq == false and positive ==> noop
					if (eq == EqualityProxy.getTrueProxy()) {
						if (positive) {
							mCollector.setTrue();
						} else {
							// rewrite (= (= lhs rhs) true)
							rewrite = mTracker.congruence(rewrite, new Term[] { mTracker.intern(at, mTheory.mTrue) });
							// rewrite (= (not true) false)
							rewrite = mUtils.convertNot(rewrite);
							mCollector.addRewrite(rewrite);
							mCollector.setSimpOr();
						}
						return;
					}
					if (eq == EqualityProxy.getFalseProxy()) {
						if (positive) {
							rewrite = mTracker.transitivity(rewrite, mTracker.intern(at, theory.mFalse));
							mCollector.addRewrite(rewrite);
							mCollector.setSimpOr();
						} else {
							mCollector.setTrue();
						}
						return;
					}
					atom = eq.getLiteral(mCollector.getSource());
					atomRewrite = mTracker.intern(at, atom.getSMTFormula(theory, true));
				} else if (at.getFunction().getName().equals("<=")) {
					// (<= SMTAffineTerm 0)
					atom = createLeq0(at, mCollector.getSource());
					atomRewrite = mTracker.intern(at, atom.getSMTFormula(theory, true));
				} else if (!at.getFunction().isIntern() || at.getFunction().getName().equals("select")) {
					atom = createBooleanLit(at, mCollector.getSource());
					atomRewrite = mTracker.intern(at, atom.getSMTFormula(theory, true));
				} else {
					atom = getLiteral(idx, positive, mCollector.getSource()).getAtom();
					atomRewrite = mTracker.intern(at, atom.getSMTFormula(theory, true));
				}
				if (positive) {
					rewrite = mTracker.transitivity(rewrite, atomRewrite);
				} else {
					rewrite = mTracker.congruence(rewrite, new Term[] { atomRewrite });
					if (atom != atom.getAtom()) {
						/* (not (<= -x 0)) can be rewritten to (not (not (< x 0))); remove double negation */
						rewrite = mUtils.convertNot(rewrite);
					}
				}
				mCollector.addLiteral(positive ? atom : atom.negate(), rewrite);
			} else if (idx instanceof QuantifiedFormula) {
				throw new UnsupportedOperationException("Quantified formula not supported");
			} else {
				throw new SMTLIBException("Cannot handle literal " + mTerm);
			}
		}
	}

	private class BuildClause implements Operation {
		private boolean mIsTrue = false;
		private final LinkedHashSet<Literal> mLits = new LinkedHashSet<Literal>();
		private final HashSet<Term> mFlattenedOrs = new HashSet<Term>();
		private final ArrayList<Term> mRewrites = new ArrayList<Term>();
		private final Term mTerm;
		private boolean mSimpOr;
		private final SourceAnnotation mSource;

		public BuildClause(final Term clauseWithProof, final SourceAnnotation proofNode) {
			mTerm = clauseWithProof;
			mSource = proofNode;
		}

		public SourceAnnotation getSource() {
			return mSource;
		}

		public void addFlatten(final Term term) {
			mFlattenedOrs.add(term);
		}

		public void addRewrite(final Term rewrite) {
			mRewrites.add(rewrite);
		}

		public void addLiteral(final Literal lit, final Term rewrite) {
			addRewrite(rewrite);
			if (mLits.add(lit)) {
				mIsTrue |= mLits.contains(lit.negate());
			} else {
				mSimpOr = true;
			}
		}

		/**
		 * Add a literal to the clause. This version should only be used if merges on the literal are impossible or
		 * already taken care of. This function records trivial satisfiability of the clause and takes care or the proof
		 * tracker to restore duplicated intern-steps on merges of the literal. Furthermore, it remembers to perform
		 * delayed clause simplification.
		 *
		 * @param lit
		 *            The literal to add to the clause.
		 */
		public void addLiteral(final Literal lit) {
			addLiteral(lit, mTracker.reflexivity(lit.getSMTFormula(mTerm.getTheory(), true)));
		}

		public void setTrue() {
			mIsTrue = true;
		}

		@Override
		public void perform() {
			if (!mIsTrue) {
				Term rewrite = mTracker.reflexivity(mTracker.getProvedTerm(mTerm));
				if (mFlattenedOrs.size() > 1) {
					rewrite = mTracker.flatten(rewrite, mFlattenedOrs);
				}
				if (mRewrites.size() > 0) {
					if (mFlattenedOrs.isEmpty()) {
						/* there was no or at all and there is only one rewrite of the formula. */
						assert mRewrites.size() == 1;
						rewrite = mTracker.transitivity(rewrite, mRewrites.get(0));
					} else {
						/* rewrite the (or ...) formula with a congruence lemma. */
						rewrite = mTracker.congruence(rewrite, mRewrites.toArray(new Term[mRewrites.size()]));
					}
				}
				final Literal[] lits = mLits.toArray(new Literal[mLits.size()]);
				/* simplify or, but only if the term wasn't already false */
				if (mTracker.getProvedTerm(rewrite) != rewrite.getTheory().mFalse && mSimpOr) {
					rewrite = mTracker.orSimpClause(rewrite, lits);
				}
				Term proof = mTracker.getRewriteProof(mTerm, rewrite);
				proof = mTracker.getClauseProof(proof);
				addClause(lits, null, getProofNewSource(proof, mSource));
			}
		}

		public void setSimpOr() {
			mSimpOr = true;
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
			private final SharedTerm mIte;

			public CollectConditions(final ConditionChain conds, final Term term, final SharedTerm ite) {
				mConds = conds;
				mTerm = term;
				mIte = ite;
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
						pushOperation(new CollectConditions(new ConditionChain(mConds, c, false), t, mIte));
						pushOperation(new CollectConditions(new ConditionChain(mConds, c, true), e, mIte));
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
				literals[mConds.size()] = theory.term("=", mIte.getTerm(), mTerm);
				Term orTerm = theory.term("or", literals);
				Term axiom = mTracker.auxAxiom(orTerm, ProofConstants.AUX_TERM_ITE);

				/* remove double negations; these may be in conflict with flatten */
				final Term orRewrite = mUtils.convertFuncNot(mTracker.reflexivity(orTerm));
				axiom = mTracker.getRewriteProof(axiom, orRewrite);
				orTerm = mTracker.getProvedTerm(axiom);

				buildClause(axiom, mSource);
			}
		}

		private final SharedTerm mTermITE;

		public AddTermITEAxiom(final SharedTerm termITE, final SourceAnnotation source) {
			mTermITE = termITE;
			mSource = source;
		}

		@Override
		public void perform() {
			pushOperation(new CollectConditions(new ConditionChain(), mTermITE.getTerm(), mTermITE));
		}
	}

	// Term creation
	public MutableAffinTerm createMutableAffinTerm(final SharedTerm term) {
		final MutableAffinTerm res = new MutableAffinTerm();
		term.shareWithLinAr();
		res.add(term.getFactor(), term.getLinVar());
		res.add(term.getOffset());
		return res;
	}

	MutableAffinTerm createMutableAffinTerm(final SMTAffineTerm at, final SourceAnnotation source) {
		final MutableAffinTerm res = new MutableAffinTerm();
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

	public SharedTerm getSharedTerm(final Term t, final SourceAnnotation source) {
		return getSharedTerm(t, false, source);
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
				if (t.getSort() == t.getTheory().getBooleanSort()) {
					addExcludedMiddleAxiom(res, source);
				} else {
					final FunctionSymbol fs = at.getFunction();
					if (fs.isInterpreted()) {
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

	private static boolean needCCTerm(final FunctionSymbol fs) {
		return !fs.isInterpreted() || fs.getName() == "select" || fs.getName() == "store" || fs.getName() == "@diff"
				|| fs.getName() == "const";
	}

	/// Internalization stuff
	private final FormulaUnLet mUnlet = new FormulaUnLet();
	private final TermCompiler mCompiler = new TermCompiler();
	private final OccurrenceCounter mOccCounter = new OccurrenceCounter();
	private final Deque<Operation> mTodoStack = new ArrayDeque<Clausifier.Operation>();

	private final Theory mTheory;
	private final DPLLEngine mEngine;
	private CClosure mCClosure;
	private LinArSolve mLASolver;
	private ArrayTheory mArrayTheory;

	private boolean mInstantiationMode;
	/**
	 * Mapping from Boolean terms to information about clauses produced for these terms.
	 */
	private final Map<Term, ClausifierInfo> mClauseData = new HashMap<Term, ClausifierInfo>();
	/**
	 * Mapping from Boolean base terms to literals. A term is considered a base term when it corresponds to an atom or
	 * its negation.
	 */
	private final Map<Term, Literal> mLiteralData = new HashMap<Term, Literal>();
	/**
	 * We cache the SharedTerms for true and false here to be able to quickly create excluded middle axioms.
	 */
	SharedTerm mSharedTrue, mSharedFalse;

	/// Statistics stuff
	@SuppressWarnings("unused")
	private int mNumAtoms = 0;

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
	final ScopedArrayList<SharedTerm> mUnshareCC = new ScopedArrayList<SharedTerm>();
	/**
	 * Keep all shared terms that need to be unshared from linear arithmetic when the top level is popped off the
	 * assertion stack.
	 */
	final ScopedArrayList<SharedTerm> mUnshareLA = new ScopedArrayList<SharedTerm>();
	/**
	 * Mapping from terms to their corresponding shared terms.
	 */
	final ScopedHashMap<Term, SharedTerm> mSharedTerms = new ScopedHashMap<Term, SharedTerm>();
	/**
	 * Map of differences to equality proxies.
	 */
	final ScopedHashMap<SMTAffineTerm, EqualityProxy> mEqualities = new ScopedHashMap<SMTAffineTerm, EqualityProxy>();
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
	private boolean mWarnedFailedPush = false;

	private final LogProxy mLogger;
	/**
	 * A tracker for proof production.
	 */
	private final IProofTracker mTracker;
	private final Utils mUtils;

	public Clausifier(final DPLLEngine engine, final int proofLevel) {
		mTheory = engine.getSMTTheory();
		mEngine = engine;
		mLogger = engine.getLogger();
		mTracker = proofLevel == 2 ? new ProofTracker() : new NoopProofTracker();
		mUtils = new Utils(mTracker);
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
	 * <li>is a {@link QuantifiedFormula} that is universally quantified</li>
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

	public void buildAuxClause(final Literal auxlit, Term axiom, final SourceAnnotation source) {
		ApplicationTerm orTerm = (ApplicationTerm) mTracker.getProvedTerm(axiom);
		assert orTerm.getFunction().getName() == "or";
		assert orTerm.getParameters()[0] == auxlit.getSMTFormula(orTerm.getTheory(), true);

		/* first remove double negations; these may be in conflict with flatten */
		final Term orRewrite = mUtils.convertFuncNot(mTracker.reflexivity(orTerm));
		axiom = mTracker.getRewriteProof(axiom, orRewrite);
		orTerm = (ApplicationTerm) mTracker.getProvedTerm(axiom);

		final BuildClause bc = new BuildClause(axiom, source);
		pushOperation(bc);
		/* tell the clause that the outer or got flattened. */
		bc.addFlatten(orTerm);
		/* add auxlit directly to prevent it getting converted. No rewrite proof necessary */
		bc.addLiteral(auxlit);
		/* use the usual engine to create the other literals of the axiom. */
		final Term[] params = orTerm.getParameters();
		for (int i = params.length - 1; i >= 1; i--) {
			pushOperation(new CollectLiterals(params[i], bc));
		}
		return;
	}

	public void buildClause(final Term term, final SourceAnnotation source) {
		final BuildClause bc = new BuildClause(term, source);
		pushOperation(bc);
		pushOperation(new CollectLiterals(mTracker.getProvedTerm(term), bc));
		return;
	}

	public void addStoreAxiom(final ApplicationTerm store, final SourceAnnotation source) {
		final Theory theory = store.getTheory();
		final Term i = store.getParameters()[1];
		final Term v = store.getParameters()[2];
		final Term axiom = theory.term("=", theory.term("select", store, i), v);
		buildClause(mTracker.auxAxiom(axiom, ProofConstants.AUX_ARRAY_STORE), source);
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
		final Literal lit = createBooleanLit((ApplicationTerm) litTerm, source);
		final Literal trueLit = trueProxy.getLiteral(source);
		final Literal falseLit = falseProxy.getLiteral(source);
		final Term trueTerm = trueLit.getSMTFormula(theory);
		final Term falseTerm = falseLit.getSMTFormula(theory);
		// m_Term => thenForm is (not m_Term) \/ thenForm
		Term axiom = mTracker.auxAxiom(theory.term("or", theory.term("not", litTerm), trueTerm),
				ProofConstants.AUX_EXCLUDED_MIDDLE_1);
		BuildClause bc = new BuildClause(axiom, source);
		bc.addFlatten(mTracker.getProvedTerm(axiom));
		final Term litRewrite = mTracker.intern(litTerm, lit.getSMTFormula(theory, true));
		Term rewrite =
				mTracker.congruence(mTracker.reflexivity(mTheory.term("not", litTerm)), new Term[] { litRewrite });
		bc.addLiteral(lit.negate(), rewrite);
		rewrite = mTracker.intern(trueTerm, trueLit.getSMTFormula(theory, true));
		bc.addLiteral(trueLit, rewrite);
		pushOperation(bc);
		// (not m_Term) => elseForm is m_Term \/ elseForm
		axiom = mTracker.auxAxiom(theory.term("or", litTerm, falseTerm), ProofConstants.AUX_EXCLUDED_MIDDLE_2);
		bc = new BuildClause(axiom, source);
		bc.addFlatten(mTracker.getProvedTerm(axiom));
		bc.addLiteral(lit, litRewrite);
		rewrite = mTracker.intern(falseTerm, falseLit.getSMTFormula(theory, true));
		bc.addLiteral(falseLit, rewrite);
		pushOperation(bc);
	}

	NamedAtom createAnonAtom(final Term smtFormula) {
		final NamedAtom atom = new NamedAtom(smtFormula, mStackLevel);
		mEngine.addAtom(atom);
		mNumAtoms++;
		return atom;
	}

	BooleanVarAtom createBooleanVar(final Term smtFormula) {
		final BooleanVarAtom atom = new BooleanVarAtom(smtFormula, mStackLevel);
		mUndoTrail = new RemoveAtom(mUndoTrail, smtFormula);
		mEngine.addAtom(atom);
		mNumAtoms++;
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

	Literal getLiteral(final Term idx, final boolean pos, final SourceAnnotation source) {
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
		final Literal lit = ci.getLiteral();
		if (pos) {
			if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED)) {
				pushOperation(new AddAuxAxioms(idx, true, source));
			}
			return lit;
		} else {
			if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED)) {
				pushOperation(new AddAuxAxioms(idx, false, source));
			}
			return lit.negate();
		}
	}

	Literal getLiteralTseitin(final Term t, final SourceAnnotation source) {
		final Term idx = toPositive(t);
		final boolean pos = t == idx;
		ClausifierInfo ci = mClauseData.get(idx);
		if (ci == null) {
			ci = new ClausifierInfo();
			mClauseData.put(idx, ci);
			mUndoTrail = new RemoveClausifierInfo(mUndoTrail, idx);
		}
		if (ci.getLiteral() == null) {
			final Literal lit = createAnonAtom(idx);
			ci.setLiteral(lit);
			mUndoTrail = new RemoveLiteral(mUndoTrail, ci);
		}
		if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED)) {
			pushOperation(new AddAuxAxioms(idx, true, source));
		}
		if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED)) {
			pushOperation(new AddAuxAxioms(idx, false, source));
		}
		return pos ? ci.getLiteral() : ci.getLiteral().negate();
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
		if (mInstantiationMode) {
			// TODO Add instantiation clauses to DPLL
		} else {
			mEngine.addFormulaClause(lits, proof, hook);
		}
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
			if (mStackLevel != 0) {
				mUndoTrail = new RemoveTheory(mUndoTrail);
			}
			mSharedTrue = new SharedTerm(this, mTheory.mTrue);
			mSharedTrue.mCCterm = mCClosure.createAnonTerm(mSharedTrue);
			mSharedTerms.put(mTheory.mTrue, mSharedTrue);
			mSharedFalse = new SharedTerm(this, mTheory.mFalse);
			mSharedFalse.mCCterm = mCClosure.createAnonTerm(mSharedFalse);
			mSharedTerms.put(mTheory.mFalse, mSharedFalse);
			final Literal atom = mCClosure.createCCEquality(mStackLevel, mSharedTrue.mCCterm, mSharedFalse.mCCterm);
			final Term trueEqFalse = mTheory.term("=", mTheory.mTrue, mTheory.mFalse);
			final Term axiom = mTracker.auxAxiom(mTheory.not(trueEqFalse), ProofConstants.AUX_TRUE_NOT_FALSE);
			final BuildClause bc = new BuildClause(axiom, SourceAnnotation.EMPTY_SOURCE_ANNOT);
			Term rewrite = mTracker.intern(trueEqFalse, atom.getSMTFormula(mTheory, true));
			rewrite = mTracker.congruence(mTracker.reflexivity(mTheory.not(trueEqFalse)), new Term[] { rewrite });
			bc.addLiteral(atom.negate(), rewrite);
			bc.perform();
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

	public void setLogic(final Logics logic) {
		if (logic.isUF() || logic.isArray()) {
			setupCClosure();
		}
		if (logic.isArithmetic()) {
			setupLinArithmetic();
		}
		if (logic.isArray()) {
			setupArrayTheory();
		}
	}

	public Iterable<BooleanVarAtom> getBooleanVars() {
		return new Iterable<BooleanVarAtom>() {

			@Override
			public Iterator<BooleanVarAtom> iterator() {
				return new BooleanVarIterator(mLiteralData.values().iterator());
			}
		};
	}

	private static final class BooleanVarIterator implements Iterator<BooleanVarAtom> {
		private final Iterator<Literal> mIt;
		private BooleanVarAtom mNext;

		public BooleanVarIterator(final Iterator<Literal> it) {
			mIt = it;
			computeNext();
		}

		private final void computeNext() {
			while (mIt.hasNext()) {
				final Literal lit = mIt.next();
				if (lit instanceof BooleanVarAtom) {
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
		while (!mTodoStack.isEmpty()) {
			if (mEngine.isTerminationRequested()) {
				/* Note: Engine remembers incompleteness */
				mTodoStack.clear();
				return;
			}
			final Operation op = mTodoStack.pop();
			op.perform();
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
		if (mEngine.inconsistent()) {
			mLogger.warn("Already inconsistent.");
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
		mInstantiationMode = false;
		run();
		mOccCounter.reset(simpFormula);
		simpFormula = null;

		// logger.info("Added " + numClauses + " clauses, " + numAtoms
		// + " auxiliary atoms.");
	}

	public void push() {
		if (mEngine.inconsistent()) {
			if (!mWarnedFailedPush) {
				mLogger.warn("Already inconsistent.");
				mWarnedFailedPush = true;
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
		mWarnedFailedPush = false;
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
		Literal lit;
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
		if (!pos) {
			lit = lit.negate();
		}
		for (final String name : names) {
			mEngine.trackAssignment(name, lit);
		}
	}

	private Literal createLeq0(final ApplicationTerm leq0term, final SourceAnnotation source) {
		Literal lit = mLiteralData.get(leq0term);
		if (lit == null) {
			final SMTAffineTerm sum = new SMTAffineTerm(leq0term.getParameters()[0]);
			final MutableAffinTerm msum = createMutableAffinTerm(sum, source);
			lit = mLASolver.generateConstraint(msum, false);
			mLiteralData.put(leq0term, lit);
			mUndoTrail = new RemoveAtom(mUndoTrail, leq0term);
		}
		return lit;
	}

	private Literal createBooleanLit(final ApplicationTerm term, final SourceAnnotation source) {
		Literal lit = mLiteralData.get(term);
		if (lit == null) {
			if (term.getParameters().length == 0) {
				lit = createBooleanVar(term);
			} else {
				final SharedTerm st = getSharedTerm(term, source);
				final EqualityProxy eq = createEqualityProxy(st, mSharedTrue);
				// Safe since m_Term is neither true nor false
				assert eq != EqualityProxy.getTrueProxy();
				assert eq != EqualityProxy.getFalseProxy();
				lit = eq.getLiteral(source);
			}
			mLiteralData.put(term, lit);
			mUndoTrail = new RemoveAtom(mUndoTrail, term);
		}
		return lit;
	}

	public boolean resetBy0Seen() {
		return mCompiler.resetBy0Seen();
	}

	public IProofTracker getTracker() {
		return mTracker;
	}

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
			res = createBooleanLit(at, source);
		} else if (at == mTheory.mTrue) {
			res = new TrueAtom();
		} else if (at == mTheory.mFalse) {
			res = new TrueAtom().negate();
		} else if (fs.getName().equals("=")) {
			if (at.getParameters()[0].getSort() == mTheory.getBooleanSort()) {
				res = getLiteralTseitin(at, source);
			} else {
				final EqualityProxy ep = createEqualityProxy(getSharedTerm(at.getParameters()[0], source),
						getSharedTerm(at.getParameters()[1], source));
				if (ep == EqualityProxy.getFalseProxy()) {
					res = new TrueAtom().negate();
				} else if (ep == EqualityProxy.getTrueProxy()) {
					res = new TrueAtom();
				} else {
					res = ep.getLiteral(source);
				}
			}
		} else if (fs.getName().equals("<=")) {
			res = createLeq0(at, source);
		} else {
			res = getLiteralTseitin(at, source);
		}

		mInstantiationMode = false;
		run();
		mOccCounter.reset(tmp2);
		tmp2 = null;
		return negated ? res.negate() : res;
	}

	public static boolean shouldFlatten(final ApplicationTerm term) {
		return term.getFunction().getName() == "or" && term.mTmpCtr <= Config.OCC_INLINE_THRESHOLD;
	}
}
