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
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
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
 * @author Juergen Christ
 */
public class Clausifier {

	/**
	 * Helper class to add the index-axiom for (store a i v), i.e., (select (store a i v) i) = v. Additionally, this
	 * class creates an array read (select a i).
	 *
	 * @author Juergen Christ
	 */
	private final class AddStoreAxioms implements Operation {

		private final ApplicationTerm mStore;

		public AddStoreAxioms(final ApplicationTerm store) {
			mStore = store;
		}

		@Override
		public void perform() {
			final IProofTracker sub = mTracker.getDescendent();
			final Term i = mStore.getParameters()[1];
			final Term v = mStore.getParameters()[2];
			final Term selstore = mTheory.term("select", mStore, i);
			final EqualityProxy ep = createEqualityProxy(getSharedTerm(selstore), getSharedTerm(v));
			final Literal lit = ep.getLiteral();
			final Term prf = sub.auxAxiom(ProofConstants.AUX_ARRAY_STORE, null, mStore, null, null);
			addClause(new Literal[] { lit }, null, getProofNewSource(ProofConstants.AUX_ARRAY_STORE, sub.clause(prf)));
			if (Config.ARRAY_ALWAYS_ADD_READ
					// HACK: We meen "finite sorts"
					|| v.getSort() == mTheory.getBooleanSort()) {
				final Term a = mStore.getParameters()[0];
				final Term sel = mTheory.term("select", a, i);
				// Simply create the CCTerm
				getSharedTerm(sel);
			}
		}

	}

	/**
	 * Helper class to insert instantiations of the array diff extensionality axiom into the clause set.
	 *
	 * @author Juergen Christ
	 */
	private final class AddDiffAxiom implements Operation {

		private final ApplicationTerm mDiff;

		public AddDiffAxiom(final ApplicationTerm diff) {
			mDiff = diff;
		}

		@Override
		public void perform() {
			// Create a = b \/ select(a, diff(a,b)) != select(b, diff(a,b))
			final Term a = mDiff.getParameters()[0];
			final Term b = mDiff.getParameters()[1];
			final SharedTerm sharedA = getSharedTerm(a);
			final SharedTerm sharedB = getSharedTerm(b);
			final EqualityProxy eparray = createEqualityProxy(sharedA, sharedB);
			if (eparray == EqualityProxy.getTrueProxy()) {
				// Someone wrote (@diff a a)...
				return;
			}
			final IProofTracker sub = mTracker.getDescendent();
			final Theory t = mDiff.getTheory();
			final Term selecta = t.term("select", a, mDiff);
			final Term selectb = t.term("select", b, mDiff);
			final SharedTerm sharedSelectA = getSharedTerm(selecta);
			final SharedTerm sharedSelectB = getSharedTerm(selectb);
			final EqualityProxy epselect = createEqualityProxy(sharedSelectA, sharedSelectB);
			final Literal[] lits = { eparray.getLiteral(), epselect.getLiteral().negate() };
			final Term prf = sub.auxAxiom(ProofConstants.AUX_ARRAY_DIFF, null, mDiff, null, null);
			addClause(lits, null, getProofNewSource(ProofConstants.AUX_ARRAY_DIFF, sub.clause(prf)));
		}

	}

	public class CCTermBuilder {
		private class BuildCCTerm implements Operation {
			private Term mTerm;

			public BuildCCTerm(final Term term) {
				mTerm = term;
			}

			@Override
			public void perform() {
				final SharedTerm shared = getSharedTerm(mTerm, true);
				if (shared.mCCterm == null) {
					final FunctionSymbol fs = getSymbol();
					if (fs == null) {
						// We have an intern function symbol
						final CCTerm res = mCClosure.createAnonTerm(shared);
						shared.setCCTerm(res);
						mConverted.push(res);
						if (mTerm.getSort().isArraySort()) {
							mArrayTheory.notifyArray(res, false);
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
				if (mTerm instanceof SMTAffineTerm) {
					mTerm = ((SMTAffineTerm) mTerm).internalize(mCompiler);
				}
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
					mArrayTheory.notifyArray(mShared.mCCterm, at.getFunction().getName().equals("store"));
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

		public CCTermBuilder() {
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

	private class RemoveAxiomProof extends TrailObject {
		private final ClausifierInfo mCi;

		public RemoveAxiomProof(final TrailObject prev, final ClausifierInfo ci) {
			super(prev);
			mCi = ci;
		}

		@Override
		public void undo() {
			mCi.clearAxiomProof();
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
		private static class ProofData {
			private final Term mTerm;
			private final Term mAxiomProof;
			private final IAnnotation mAnnot;
			private final boolean mNegated;

			public ProofData(final Term term, final Term axiomProof, final IAnnotation annot, final boolean neg) {
				mTerm = term;
				mAxiomProof = axiomProof;
				mAnnot = annot;
				mNegated = neg;
			}
		}

		static final int POS_AXIOMS_ADDED = 1;
		static final int NEG_AXIOMS_ADDED = 2;
		static final int POS_AUX_AXIOMS_ADDED = 4;
		static final int NEG_AUX_AXIOMS_ADDED = 8;
		private Literal mLit;
		private int mFlags;
		private Object mProof;

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

		public void setAxiomProof(final Term term, final Term proof, final IAnnotation annot, final boolean negated) {
			if (proof == null) {
				mProof = annot;
			} else {
				mProof = new ProofData(term, proof, annot, negated);
			}
		}

		/// Debugging only
		boolean isAxiomProofAvailable() {
			return mProof != null;
		}

		public ProofNode getAxiomProof(final IProofTracker tracker, final Term idx, final Literal lit) {
			if (mProof instanceof IAnnotation) {
				return new LeafNode(LeafNode.NO_THEORY, (IAnnotation) mProof);
			}
			final ProofData pd = (ProofData) mProof;
			final Theory t = pd.mTerm.getTheory();
			final IProofTracker sub = tracker.getDescendent();
			final Term unquoted = pd.mTerm;
			if (pd.mNegated && testFlags(ClausifierInfo.POS_AXIOMS_ADDED)) {
				sub.negation(t.term(t.mNot, unquoted), unquoted, ProofConstants.RW_NOT_SIMP);
			}
			sub.intern(idx, lit);
			return new LeafNode(LeafNode.NO_THEORY,
					new SourceAnnotation((SourceAnnotation) pd.mAnnot, sub.clause(pd.mAxiomProof)));
		}

		public void clearAxiomProof() {
			mProof = null;
		}
	}

	private interface Operation {
		public void perform();
	}

	private class AddAsAxiom implements Operation {
		/**
		 * The proof so far.
		 */
		private final Term mProofTerm;
		/**
		 * The term to add as axiom.
		 */
		private final Term mTerm;
		/**
		 * The polarity (true means negated).
		 */
		private final boolean mNegated;

		public AddAsAxiom(final Term term, final Term proofTerm) {
			this(term, false, proofTerm);
		}

		public AddAsAxiom(final Term term, final boolean negated, final Term proofTerm) {
			mTerm = term;
			mNegated = negated;
			mProofTerm = proofTerm;
		}

		@Override
		public void perform() {
			final Term idx = toPositive(mTerm);
			final ClausifierInfo ci = getInfo(idx);
			// idx != m_Term ==> additional negation
			// idx == m_Term ==> no additional negation
			final boolean positive = idx == mTerm ^ mNegated;
			int flag, auxflag, negflag;
			if (positive) {
				flag = ClausifierInfo.POS_AXIOMS_ADDED;
				auxflag = ClausifierInfo.POS_AUX_AXIOMS_ADDED;
				negflag = ClausifierInfo.NEG_AXIOMS_ADDED;
			} else {
				flag = ClausifierInfo.NEG_AXIOMS_ADDED;
				auxflag = ClausifierInfo.NEG_AUX_AXIOMS_ADDED;
				negflag = ClausifierInfo.POS_AXIOMS_ADDED;
			}
			if (ci.testFlags(flag)) {
				// We've already added this formula as axioms
				return;
			}
			// if (ci.testFlags(negflag)) {
			// // We've added the negation as axiom => Create empty clause
			// if (mEngine.isProofGenerationEnabled()) {
			// // (@res sourceAnnot ci.getAxiomProof)
			// Clause primary;
			// Antecedent ante;
			// final NamedAtom idxAtom = new NamedAtom(idx, mStackLevel);
			// mTracker.quoted(idx, idxAtom);
			// if (positive) {
			// primary = new Clause(new Literal[] { idxAtom }, getClauseProof(mProofTerm));
			// ante = new Antecedent(idxAtom.negate(), new Clause(new Literal[] { idxAtom.negate() },
			// ci.getAxiomProof(mTracker, idx, idxAtom)));
			// } else {
			// primary = new Clause(new Literal[] { idxAtom }, ci.getAxiomProof(mTracker, idx, idxAtom));
			// ante = new Antecedent(idxAtom.negate(),
			// new Clause(new Literal[] { idxAtom.negate() }, getClauseProof(mProofTerm)));
			// }
			// final ResolutionNode rn = new ResolutionNode(primary, new Antecedent[] { ante });
			// addClause(new Literal[0], null, rn);
			// } else {
			// addClause(new Literal[0], null, mProof);
			// }
			// return;
			// }
			// assert !ci.isAxiomProofAvailable();
			// ci.setAxiomProof(mTerm, mProofTerm, getAnnotation(), !positive);
			// mUndoTrail = new RemoveAxiomProof(mUndoTrail, ci);
			final Literal auxlit = ci.getLiteral();
			if (auxlit != null) {
				if (!ci.testFlags(auxflag)) {
					new AddAuxAxioms(idx, auxlit, positive).perform();
				}
				mTracker.quoted(idx, auxlit.getAtom());
				addClause(new Literal[] { positive ? auxlit : auxlit.negate() }, null, getClauseProof(mProofTerm));
				ci.setFlag(flag);
				mUndoTrail = new RemoveFlag(mUndoTrail, ci, flag);
				return;
			}
			ci.setFlag(flag);
			mUndoTrail = new RemoveFlag(mUndoTrail, ci, flag);
			final Theory t = mTerm.getTheory();
			if (idx instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) idx;
				if (at.getFunction() == t.mOr) {
					if (positive) {
						final BuildClause bc = new BuildClause(mProofTerm, at);
						bc.setOrigArgs(at.getParameters());
						pushOperation(bc);
						for (final Term p : at.getParameters()) {
							pushOperation(new CollectLiterals(p, bc));
						}
					} else {
						for (final Term p : at.getParameters()) {
							pushOperation(new AddAsAxiom(p, true,
									mTracker.split(p, mProofTerm, ProofConstants.SPLIT_NEG_OR)));
						}
					}
				} else if ((!at.getFunction().isIntern() || at.getFunction().getName().equals("select"))
						&& at.getFunction().getReturnSort() == t.getBooleanSort()) {
					final Literal lit = createBooleanLit(at);
					final IProofTracker sub = mTracker.getDescendent();
					sub.intern(at, lit);
					addClause(new Literal[] { positive ? lit : lit.negate() }, null,
							getProofNewSource(sub.clause(mProofTerm)));
				} else if (at.getFunction().getName().equals("=")) {
					final Term lhs = at.getParameters()[0];
					final Term rhs = at.getParameters()[1];
					if (lhs.getSort() == t.getBooleanSort()) {
						final BuildClause bc1 = new BuildClause(LeafNode.NO_THEORY);
						pushOperation(bc1);
						Term t1, t2;
						if (positive) {
							bc1.setProofTerm(mTracker.split(at, mProofTerm, ProofConstants.SPLIT_POS_EQ_1));
							pushOperation(new CollectLiterals(lhs, bc1));
							pushOperation(new CollectLiterals(t2 = new Utils(bc1.getTracker()).createNot(rhs), bc1));
							bc1.setOrigArgs(lhs, t2);
						} else {
							bc1.setProofTerm(mTracker.split(at, mProofTerm, ProofConstants.SPLIT_NEG_EQ_1));
							pushOperation(new CollectLiterals(lhs, bc1));
							pushOperation(new CollectLiterals(rhs, bc1));
							bc1.setOrigArgs(lhs, rhs);
						}
						bc1.getTracker().markPosition();
						final BuildClause bc2 = new BuildClause(LeafNode.NO_THEORY);
						pushOperation(bc2);
						final Utils tmp = new Utils(bc2.getTracker());
						if (positive) {
							bc2.setProofTerm(mTracker.split(at, mProofTerm, ProofConstants.SPLIT_POS_EQ_2));
							pushOperation(new CollectLiterals(t1 = tmp.createNot(lhs), bc2));
							pushOperation(new CollectLiterals(rhs, bc2));
							bc2.setOrigArgs(t1, rhs);
						} else {
							bc2.setProofTerm(mTracker.split(at, mProofTerm, ProofConstants.SPLIT_NEG_EQ_2));
							pushOperation(new CollectLiterals(t1 = tmp.createNot(lhs), bc2));
							pushOperation(new CollectLiterals(t2 = tmp.createNot(rhs), bc2));
							bc2.setOrigArgs(t1, t2);
						}
						bc2.getTracker().markPosition();
					} else {
						final SharedTerm slhs = getSharedTerm(lhs);
						final SharedTerm srhs = getSharedTerm(rhs);
						final EqualityProxy eq = createEqualityProxy(slhs, srhs);
						// eq == true and positive ==> return
						// eq == true and !positive ==> addClause({})
						// eq == false and !positive ==> return
						// eq == false and positive ==> addClause({})
						if (eq == EqualityProxy.getTrueProxy()) {
							if (!positive) {
								mTracker.eq(lhs, rhs, mTheory.mTrue);
								mTracker.negation(mTheory.mTrue, mTheory.mFalse, ProofConstants.RW_NOT_SIMP);
								addClause(new Literal[0], null, getClauseProof(mProofTerm));
							}
							return;
						}
						if (eq == EqualityProxy.getFalseProxy()) {
							if (positive) {
								mTracker.eq(lhs, rhs, mTheory.mFalse);
								addClause(new Literal[0], null, getClauseProof(mProofTerm));
							}
							return;
						}
						final Literal lit = eq.getLiteral();
						final IProofTracker sub = mTracker.getDescendent();
						sub.intern(at, lit);
						addClause(new Literal[] { positive ? lit : lit.negate() }, null,
								getProofNewSource(sub.clause(mProofTerm)));
					}
				} else if (at.getFunction().getName().equals("ite")) {
					assert at.getFunction().getReturnSort() == t.getBooleanSort();
					final Term cond = at.getParameters()[0];
					Term thenForm = at.getParameters()[1];
					Term elseForm = at.getParameters()[2];
					int kind1 = ProofConstants.SPLIT_POS_ITE_1;
					int kind2 = ProofConstants.SPLIT_POS_ITE_2;
					BuildClause bc1, bc2;
					Term t1;
					if (!positive) {
						kind1 = ProofConstants.SPLIT_NEG_ITE_1;
						kind2 = ProofConstants.SPLIT_NEG_ITE_2;
					}
					bc1 = new BuildClause(LeafNode.NO_THEORY);
					bc1.setProofTerm(mTracker.split(at, mProofTerm, kind1));
					Utils tmp1 = new Utils(bc1.getTracker());
					pushOperation(bc1);
					pushOperation(new CollectLiterals(t1 = tmp1.createNot(cond), bc1));
					if (!positive) {
						thenForm = tmp1.createNot(thenForm);
					}
					bc1.setOrigArgs(t1, thenForm);
					tmp1 = null;
					pushOperation(new CollectLiterals(thenForm, bc1));
					bc1.getTracker().markPosition();
					bc2 = new BuildClause(LeafNode.NO_THEORY);
					bc2.setProofTerm(mTracker.split(at, mProofTerm, kind2));
					Utils tmp2 = new Utils(bc2.getTracker());
					pushOperation(bc2);
					pushOperation(new CollectLiterals(cond, bc2));
					if (!positive) {
						elseForm = tmp2.createNot(elseForm);
					}
					bc2.setOrigArgs(cond, elseForm);
					tmp2 = null;
					pushOperation(new CollectLiterals(elseForm, bc2));
					bc2.getTracker().markPosition();
				} else if (at.getFunction().getName().equals("<=")) {
					// (<= SMTAffineTerm 0)
					final Literal lit = createLeq0(at);
					final IProofTracker sub = mTracker.getDescendent();
					sub.intern(at, lit);
					if (lit.getSign() == -1 && !positive) {
						sub.negateLit(lit, mTheory);
					}
					addClause(new Literal[] { positive ? lit : lit.negate() }, null,
							getProofNewSource(sub.clause(mProofTerm)));
				} else if (at == t.mTrue) {
					// Nothing to do...
				} else if (at == t.mFalse) {
					addClause(new Literal[0], null, getClauseProof(mProofTerm));
				} else {
					throw new InternalError("Not implementd: " + SMTAffineTerm.cleanup(at));
				}
			} else if (idx instanceof QuantifiedFormula) {
				// TODO Fix Quantifiers once supported
				throw new SMTLIBException("Cannot create quantifier in quantifier-free logic");
			} else {
				throw new InternalError("Don't know how to convert into axiom: " + SMTAffineTerm.cleanup(mTerm));
			}
		}

	}

	private class AddAuxAxioms implements Operation {

		private final Term mTerm;
		private final Literal mAuxLit;
		private final boolean mPositive;

		public AddAuxAxioms(final Term term, final Literal lit, final boolean pos) {
			assert term == toPositive(term);
			mTerm = term;
			mAuxLit = lit;
			mPositive = pos;
		}

		@Override
		public void perform() {
			final ClausifierInfo ci = getInfo(mTerm);
			int auxflag, flag, negflag;
			if (mPositive) {
				auxflag = ClausifierInfo.POS_AUX_AXIOMS_ADDED;
				flag = ClausifierInfo.POS_AXIOMS_ADDED;
				negflag = ClausifierInfo.NEG_AXIOMS_ADDED;
			} else {
				auxflag = ClausifierInfo.NEG_AUX_AXIOMS_ADDED;
				flag = ClausifierInfo.NEG_AXIOMS_ADDED;
				negflag = ClausifierInfo.POS_AXIOMS_ADDED;
			}
			if (ci.testFlags(auxflag)) {
				// We've already added the aux axioms
				// Nothing to do
				return;
			}
			if (ci.testFlags(flag)) {
				/*
				 * If we know that the axiom already holds, the aux axioms trivially simplify to true. Hence, we don't
				 * need them at all.
				 */
				return;
			}
			ci.setFlag(auxflag);
			mUndoTrail = new RemoveFlag(mUndoTrail, ci, auxflag);
			// if (ci.testFlags(negflag)) {
			// // simplify by asserting the proxy as unit.
			// final Literal[] unit = new Literal[] { mPositive ? mAuxLit.negate() : mAuxLit };
			// if (mEngine.isProofGenerationEnabled()) {
			// addClause(unit, null, ci.getAxiomProof(mTracker, mTerm, mAuxLit));
			// } else {
			// addClause(unit, null, mProof);
			// }
			// return;
			// }
			final Theory t = mTerm.getTheory();
			if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) mTerm;
				if (at.getFunction() == t.mOr) {
					if (mPositive) {
						final BuildClause bc = new BuildClause(ProofConstants.AUX_OR_POS);
						bc.auxAxiom(mAuxLit, at, null, null);
						bc.addLiteral(mAuxLit.negate());
						bc.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit.negate(), at.getParameters()));
						pushOperation(bc);
						for (final Term param : at.getParameters()) {
							pushOperation(new CollectLiterals(param, bc));
						}
					} else {
						final CreateNegClauseAuxAxioms helper = new CreateNegClauseAuxAxioms(mAuxLit);
						pushOperation(helper);
						helper.init(mTerm);
					}
				} else if (at.getFunction().getName().equals("ite")) {
					final Term cond = at.getParameters()[0];
					final Term thenTerm = at.getParameters()[1];
					final Term elseTerm = at.getParameters()[2];
					if (mPositive) {
						Term t1;
						final BuildClause bc1 = new BuildClause(ProofConstants.AUX_ITE_POS_1);
						bc1.auxAxiom(mAuxLit, at, null, null);
						bc1.addLiteral(mAuxLit.negate());
						pushOperation(bc1);
						pushOperation(new CollectLiterals(thenTerm, bc1));
						pushOperation(new CollectLiterals(t1 = new Utils(bc1.getTracker()).createNot(cond), bc1));
						bc1.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit.negate(), t1, thenTerm));
						bc1.getTracker().markPosition();
						final BuildClause bc2 = new BuildClause(ProofConstants.AUX_ITE_POS_2);
						bc2.auxAxiom(mAuxLit, at, null, null);
						bc2.addLiteral(mAuxLit.negate());
						pushOperation(bc2);
						pushOperation(new CollectLiterals(elseTerm, bc2));
						pushOperation(new CollectLiterals(cond, bc2));
						bc2.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit.negate(), cond, elseTerm));
						bc2.getTracker().markPosition();
						if (Config.REDUNDANT_ITE_CLAUSES) {
							final BuildClause bc3 = new BuildClause(ProofConstants.AUX_ITE_POS_RED);
							bc3.auxAxiom(mAuxLit, at, null, null);
							bc3.addLiteral(mAuxLit.negate());
							pushOperation(bc3);
							pushOperation(new CollectLiterals(elseTerm, bc3));
							pushOperation(new CollectLiterals(thenTerm, bc3));
							bc3.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit.negate(), thenTerm, elseTerm));
							bc3.getTracker().markPosition();
						}
					} else {
						Term t1, t2;
						final BuildClause bc1 = new BuildClause(ProofConstants.AUX_ITE_NEG_1);
						Utils tmp1 = new Utils(bc1.getTracker());
						bc1.auxAxiom(mAuxLit, at, null, null);
						bc1.addLiteral(mAuxLit);
						pushOperation(bc1);
						pushOperation(new CollectLiterals(t2 = tmp1.createNot(thenTerm), bc1));
						pushOperation(new CollectLiterals(t1 = tmp1.createNot(cond), bc1));
						bc1.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit, t1, t2));
						bc1.getTracker().markPosition();
						tmp1 = null;
						final BuildClause bc2 = new BuildClause(ProofConstants.AUX_ITE_NEG_2);
						bc2.auxAxiom(mAuxLit, at, null, null);
						bc2.addLiteral(mAuxLit);
						pushOperation(bc2);
						pushOperation(new CollectLiterals(t1 = new Utils(bc2.getTracker()).createNot(elseTerm), bc2));
						pushOperation(new CollectLiterals(cond, bc2));
						bc2.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit, cond, t1));
						bc2.getTracker().markPosition();
						if (Config.REDUNDANT_ITE_CLAUSES) {
							final BuildClause bc3 = new BuildClause(ProofConstants.AUX_ITE_NEG_RED);
							final Utils tmp3 = new Utils(bc3.getTracker());
							bc3.auxAxiom(mAuxLit, at, null, null);
							bc3.addLiteral(mAuxLit);
							pushOperation(bc3);
							pushOperation(new CollectLiterals(t2 = tmp3.createNot(elseTerm), bc3));
							pushOperation(new CollectLiterals(t1 = tmp3.createNot(thenTerm), bc3));
							bc3.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit, t1, t2));
							bc3.getTracker().markPosition();
						}
					}
				} else if (at.getFunction().getName().equals("=")) {
					assert at.getParameters().length == 2;
					final Term lhs = at.getParameters()[0];
					final Term rhs = at.getParameters()[1];
					assert lhs.getSort() == t.getBooleanSort();
					assert rhs.getSort() == t.getBooleanSort();
					Term t1, t2;
					if (mPositive) {
						final BuildClause bc1 = new BuildClause(ProofConstants.AUX_EQ_POS_1);
						Utils tmp1 = new Utils(bc1.getTracker());
						bc1.auxAxiom(mAuxLit, at, null, null);
						bc1.addLiteral(mAuxLit.negate());
						pushOperation(bc1);
						pushOperation(new CollectLiterals(t2 = tmp1.createNot(rhs), bc1));
						pushOperation(new CollectLiterals(lhs, bc1));
						bc1.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit.negate(), lhs, t2));
						bc1.getTracker().markPosition();
						tmp1 = null;
						final BuildClause bc2 = new BuildClause(ProofConstants.AUX_EQ_POS_2);
						final Utils tmp2 = new Utils(bc2.getTracker());
						bc2.auxAxiom(mAuxLit, at, null, null);
						bc2.addLiteral(mAuxLit.negate());
						pushOperation(bc2);
						pushOperation(new CollectLiterals(rhs, bc2));
						pushOperation(new CollectLiterals(t1 = tmp2.createNot(lhs), bc2));
						bc2.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit.negate(), t1, rhs));
						bc2.getTracker().markPosition();
					} else {
						final BuildClause bc1 = new BuildClause(ProofConstants.AUX_EQ_NEG_1);
						bc1.auxAxiom(mAuxLit, at, null, null);
						bc1.addLiteral(mAuxLit);
						pushOperation(bc1);
						pushOperation(new CollectLiterals(rhs, bc1));
						pushOperation(new CollectLiterals(lhs, bc1));
						bc1.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit, lhs, rhs));
						bc1.getTracker().markPosition();
						final BuildClause bc2 = new BuildClause(ProofConstants.AUX_EQ_NEG_2);
						final Utils tmp = new Utils(bc2.getTracker());
						bc2.auxAxiom(mAuxLit, at, null, null);
						bc2.addLiteral(mAuxLit);
						pushOperation(bc2);
						pushOperation(new CollectLiterals(t2 = tmp.createNot(rhs), bc2));
						pushOperation(new CollectLiterals(t1 = tmp.createNot(lhs), bc2));
						bc2.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit, t1, t2));
						bc2.getTracker().markPosition();
					}
				} else {
					throw new InternalError("AuxAxiom not implemented: " + SMTAffineTerm.cleanup(mTerm));
				}
			} else if (mTerm instanceof QuantifiedFormula) {
				// TODO: Correctly implement this once we support quantifiers.
				throw new SMTLIBException("Cannot create quantifier in quantifier-free logic");
			} else {
				throw new InternalError("Don't know how to create aux axiom: " + SMTAffineTerm.cleanup(mTerm));
			}
		}

	}

	private class CreateNegClauseAuxAxioms implements Operation {

		Set<Term> mDisjuncts = new LinkedHashSet<>();
		private final Literal mAuxLit;

		public CreateNegClauseAuxAxioms(final Literal auxLit) {
			mAuxLit = auxLit;
		}

		public void init(final Term term) {
			// Cannot be done in ctor since CollectDisjuncts has to be before this.
			pushOperation(new CollectDisjuncts(term));
		}

		@Override
		public void perform() {
			Term t;
			for (final Term disj : mDisjuncts) {
				final BuildClause bc = new BuildClause(ProofConstants.AUX_OR_NEG);
				bc.auxAxiom(mAuxLit, disj, null, null);
				bc.addLiteral(mAuxLit);
				pushOperation(bc);
				pushOperation(new CollectLiterals(t = new Utils(bc.getTracker()).createNot(disj), bc));
				bc.getTracker().markPosition();
				bc.setOrigArgs(mTracker.produceAuxAxiom(mAuxLit, t));
			}
		}

		private class CollectDisjuncts implements Operation {

			private final Term mTerm;

			public CollectDisjuncts(final Term term) {
				mTerm = term;
			}

			@Override
			public void perform() {
				if (mTerm instanceof ApplicationTerm) {
					final ApplicationTerm at = (ApplicationTerm) mTerm;
					if (at.getFunction() == at.getTheory().mOr) {
						for (final Term disj : at.getParameters()) {
							pushOperation(new CollectDisjuncts(disj));
						}
						return;
					}
				}
				mDisjuncts.add(mTerm);
			}

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
			final Theory t = mTerm.getTheory();
			if (mTerm == t.mFalse) {
				return;
			}
			if (mTerm == t.mTrue) {
				mCollector.setTrue();
				return;
			}
			final Term idx = toPositive(mTerm);
			final boolean positive = mTerm == idx;
			// TODO What about this optimization? It increases the number of
			// conflicts on some examples, but should be better.
			// Literal knownlit = getLiteralForPolarity(idx, positive);
			// if (knownlit != null) {
			// m_Collector.addLiteral(knownlit);
			// return;
			// }
			if (idx instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) idx;
				if (positive && at.getFunction() == t.mOr) {
					if (mTerm.mTmpCtr > Config.OCC_INLINE_THRESHOLD) {
						// m_Logger.trace("Don't inline the clause" + SMTAffineTerm.cleanup(idx));
						mCollector.getTracker().save();
						final Literal lit = getLiteral(idx);
						mCollector.getTracker().quoted(idx, lit.getAtom());
						mCollector.addLiteral(lit, mTerm);
						mCollector.getTracker().cleanSave();
					} else {
						mCollector.setFlatten(at.getParameters());
						for (final Term p : at.getParameters()) {
							pushOperation(new CollectLiterals(p, mCollector));
						}
					}
				} else if ((!at.getFunction().isIntern() || at.getFunction().getName().equals("select"))
						&& at.getFunction().getReturnSort() == t.getBooleanSort()) {
					mCollector.getTracker().save();
					final Literal lit = createBooleanLit(at);
					mCollector.getTracker().intern(idx, lit);
					mCollector.addLiteral(positive ? lit : lit.negate(), mTerm);
					mCollector.getTracker().cleanSave();
					// } else if (at.getFunction().getName().equals("ite")) {
					// Term cond = at.getParameters()[0];
					// Term tc = at.getParameters()[1];
					// Term ec = at.getParameters()[2];
					// assert tc.getSort() == t.getBooleanSort();
					// // (ite cond tc ec) ===
					// // (or (and cond tc) (and (not cond) ec))
					// /*
					// * (= A B) === (or (and A B) (and (not A) (not B)))
					// */
				} else if (at.getFunction().getName().equals("=")
						&& at.getParameters()[0].getSort() != mTheory.getBooleanSort()) {
					final Term lhs = at.getParameters()[0];
					final Term rhs = at.getParameters()[1];
					final SharedTerm slhs = getSharedTerm(lhs);
					final SharedTerm srhs = getSharedTerm(rhs);
					final EqualityProxy eq = createEqualityProxy(slhs, srhs);
					// eq == true and positive ==> set to true
					// eq == true and !positive ==> noop
					// eq == false and !positive ==> set to true
					// eq == false and positive ==> noop
					if (eq == EqualityProxy.getTrueProxy()) {
						if (positive) {
							mCollector.setTrue();
						} else {
							mCollector.getTracker().eq(lhs, rhs, mTheory.mTrue);
							mCollector.getTracker().negation(mTheory.mTrue, mTheory.mFalse, ProofConstants.RW_NOT_SIMP);
							mCollector.getTracker().notifyFalseLiteral(at);
							mCollector.setSimpOr();
						}
						return;
					}
					if (eq == EqualityProxy.getFalseProxy()) {
						if (positive) {
							mCollector.getTracker().eq(lhs, rhs, mTheory.mFalse);
							mCollector.getTracker().notifyFalseLiteral(at);
							mCollector.setSimpOr();
						} else {
							mCollector.setTrue();
						}
						return;
					}
					mCollector.getTracker().save();
					final DPLLAtom eqAtom = eq.getLiteral();
					mCollector.getTracker().eq(lhs, rhs, eqAtom);
					mCollector.addLiteral(positive ? eqAtom : eqAtom.negate(), mTerm);
					mCollector.getTracker().cleanSave();
				} else if (at.getFunction().getName().equals("<=")) {
					// (<= SMTAffineTerm 0)
					mCollector.getTracker().save();
					final Literal lit = createLeq0(at);
					mCollector.getTracker().intern(at, lit);
					if (!positive && lit.getSign() == -1) {
						mCollector.getTracker().negateLit(lit, mTheory);
					}
					mCollector.addLiteral(positive ? lit : lit.negate(), mTerm);
					mCollector.getTracker().cleanSave();
				} else {
					mCollector.getTracker().save();
					final Literal lit = getLiteral(mTerm);
					mCollector.getTracker().quoted(mTerm, lit);
					mCollector.addLiteral(lit, mTerm);
					mCollector.getTracker().cleanSave();
				}
			} else {
				if (positive) {
					assert idx instanceof QuantifiedFormula;
					final Literal lit = getLiteral(idx);
					// TODO: Proof
					mCollector.addLiteral(lit, mTerm);
				} else {
					// TODO Skolemize and recurse
				}
			}
		}
	}

	private class BuildClause implements Operation {
		private boolean mIsTrue = false;
		private final int mLeafKind;
		private final LinkedHashSet<Literal> mLits = new LinkedHashSet<>();
		private Term mProofTerm;
		private Term[] mOrigArgs;
		private final IProofTracker mSubTracker = mTracker.getDescendent();
		private boolean mFlatten;
		private boolean mSimpOr;

		// @ invariant ProofProductionEnabled ==>
		// (m_LeafKind != LeafNode.NO_THEORY) == (m_ProofTerm == null);
		public BuildClause(final int leafKind) {
			mLeafKind = leafKind;
			mProofTerm = null;
		}

		public BuildClause(final Term proofTerm, final Term original) {
			this(LeafNode.NO_THEORY);
			mProofTerm = proofTerm;
		}

		public void auxAxiom(final Literal lit, final Term res, final Term base, final Object auxData) {
			mProofTerm = mSubTracker.auxAxiom(mLeafKind, lit, res, base, auxData);
		}

		public void setProofTerm(final Term proof) {
			mProofTerm = proof;
		}

		public void setOrigArgs(final Term... args) {
			mOrigArgs = args;
		}

		/**
		 * Add a literal to the clause. Use this version if merges on this literal are possible. This version notifies
		 * the proof tracker and then delegates to the non-merge function {@link #addLiteral(Literal)} to do the real
		 * work.
		 *
		 * @param lit
		 *            The literal to add to the clause.
		 * @param t
		 *            The term for which this literal has been created.
		 */
		public void addLiteral(final Literal lit, final Term t) {
			if (mSubTracker.notifyLiteral(lit, t)) {
				addLiteral(lit);
			} else {
				mSimpOr = true;
				mSubTracker.restore();
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
			if (mLits.add(lit)) {
				mIsTrue |= mLits.contains(lit.negate());
			} else {
				mSimpOr = true;
			}
		}

		public void setTrue() {
			mIsTrue = true;
		}

		@Override
		public void perform() {
			if (!mIsTrue) {
				final Literal[] lits = mLits.toArray(new Literal[mLits.size()]);
				if (mFlatten) {
					mSubTracker.flatten(mOrigArgs, mSimpOr);
				} else if (mSimpOr) {
					mSubTracker.orSimpClause(mOrigArgs);
				}
				addClause(lits, null, getProofNewSource(mLeafKind, mSubTracker.clause(mProofTerm)));
			}
		}

		public IProofTracker getTracker() {
			return mSubTracker;
		}

		public void setFlatten(final Term[] origArgs) {
			for (final Term t : origArgs) {
				if (t instanceof ApplicationTerm) {
					final ApplicationTerm at = (ApplicationTerm) t;
					if (shouldFlatten(at)) {
						mOrigArgs = origArgs;
						mFlatten = true;
						return;
					}
				}
			}
		}

		public void setSimpOr() {
			mSimpOr = true;
		}
	}

	private class AddDivideAxioms implements Operation {

		private final Term mDivTerm;
		private final Term mDivider;
		private final Rational mDivident;

		public AddDivideAxioms(final Term divTerm, final Term divider, final Rational divident) {
			mDivTerm = divTerm;
			mDivider = divider;
			mDivident = divident;
		}

		@Override
		public void perform() {
			IProofTracker sub = mTracker.getDescendent();
			Utils tmp = new Utils(sub);
			final SMTAffineTerm arg = SMTAffineTerm.create(mDivider);
			final SMTAffineTerm div = SMTAffineTerm.create(mDivTerm);
			// (<= (- (* d (div x d)) x) 0)
			final SMTAffineTerm difflow = div.mul(mDivident).add(arg.negate());
			final Literal lit1 = createLeq0((ApplicationTerm) tmp.createLeq0(difflow));
			Term prf = sub.auxAxiom(ProofConstants.AUX_DIV_LOW, null, difflow, null, null);
			sub.leq0(difflow, lit1);
			addClause(new Literal[] { lit1 }, null, getProofNewSource(ProofConstants.AUX_DIV_LOW, sub.clause(prf)));
			// (not (<= (+ |d| (- x) (* d (div x d))) 0))
			sub = mTracker.getDescendent();
			tmp = new Utils(sub);
			final SMTAffineTerm diffhigh = arg.negate().add(div.mul(mDivident)).add(mDivident.abs());
			prf = sub.auxAxiom(ProofConstants.AUX_DIV_HIGH, null, diffhigh, null, null);
			final Literal lit2 = createLeq0((ApplicationTerm) tmp.createLeq0(diffhigh));
			sub.leq0(diffhigh, lit2);
			if (lit2.getSign() == -1) {
				sub.negateLit(lit2, mTheory);
			}
			addClause(new Literal[] { lit2.negate() }, null,
					getProofNewSource(ProofConstants.AUX_DIV_HIGH, sub.clause(prf)));
		}

	}

	/**
	 * Helper to add the auxiliary axioms for to_int axioms. Since the axioms for (to_int x) equal the axioms added for
	 * (div x 1), we reuse AddDivideAxioms.
	 *
	 * @author Juergen Christ
	 */
	private class AddToIntAxioms implements Operation {

		private final ApplicationTerm mToIntTerm;

		public AddToIntAxioms(final ApplicationTerm toIntTerm) {
			mToIntTerm = toIntTerm;
		}

		@Override
		public void perform() {
			IProofTracker sub = mTracker.getDescendent();
			Utils tmp = new Utils(sub);
			final SMTAffineTerm realTerm = SMTAffineTerm.create(mToIntTerm.getParameters()[0]);
			final SMTAffineTerm toInt = SMTAffineTerm.create(mToIntTerm).typecast(realTerm.getSort());
			// (<= (- (to_real (to_int x)) x) 0)
			final SMTAffineTerm difflow = toInt.add(realTerm.negate());
			final Literal lit1 = createLeq0((ApplicationTerm) tmp.createLeq0(difflow));
			Term prf = sub.auxAxiom(ProofConstants.AUX_TO_INT_LOW, null, difflow, null, null);
			sub.leq0(difflow, lit1);
			addClause(new Literal[] { lit1 }, null, getProofNewSource(ProofConstants.AUX_TO_INT_LOW, sub.clause(prf)));
			// (not (<= (+ d (- x) (* d (div x d))) 0))
			sub = mTracker.getDescendent();
			tmp = new Utils(sub);
			final SMTAffineTerm diffhigh = toInt.add(Rational.ONE).add(realTerm.negate());
			prf = sub.auxAxiom(ProofConstants.AUX_TO_INT_HIGH, null, diffhigh, null, null);
			final Literal lit2 = createLeq0((ApplicationTerm) tmp.createLeq0(diffhigh));
			sub.leq0(diffhigh, lit2);
			if (lit2.getSign() == -1) {
				sub.negateLit(lit2, mTheory);
			}
			addClause(new Literal[] { lit2.negate() }, null,
					getProofNewSource(ProofConstants.AUX_TO_INT_HIGH, sub.clause(prf)));
		}
	}

	/**
	 * Add the axioms for the law of excluded middle. This must happen if a Boolean function is used as a parameter to a
	 * non-Boolean function.
	 *
	 * @author Juergen Christ
	 */
	private class AddExcludedMiddleAxiom implements Operation {

		private final SharedTerm mSharedTerm;

		public AddExcludedMiddleAxiom(final SharedTerm shared) {
			mSharedTerm = shared;
		}

		@Override
		public void perform() {
			final EqualityProxy thenProxy = createEqualityProxy(mSharedTerm, mSharedTrue);
			final EqualityProxy elseProxy = createEqualityProxy(mSharedTerm, mSharedFalse);
			// These asserts should hold since we do not add excluded middle
			// axioms for true or false, and the equality proxies are
			// non-numeric
			assert thenProxy != EqualityProxy.getTrueProxy();
			assert thenProxy != EqualityProxy.getFalseProxy();
			assert elseProxy != EqualityProxy.getTrueProxy();
			assert elseProxy != EqualityProxy.getFalseProxy();
			// m_Term => thenForm is (not m_Term) \/ thenForm
			final BuildClause bc1 = new BuildClause(ProofConstants.AUX_EXCLUDED_MIDDLE_1);
			final Literal lit1 = thenProxy.getLiteral();
			bc1.auxAxiom(lit1, mSharedTerm.getTerm(), null, null);
			bc1.addLiteral(lit1);
			pushOperation(bc1);
			pushOperation(new CollectLiterals(new Utils(bc1.getTracker()).createNot(mSharedTerm.getTerm()), bc1));
			// (not m_Term) => elseForm is m_Term \/ elseForm
			final BuildClause bc2 = new BuildClause(ProofConstants.AUX_EXCLUDED_MIDDLE_2);
			final Literal lit2 = elseProxy.getLiteral();
			bc2.auxAxiom(lit2, mSharedTerm.getTerm(), null, null);
			bc2.addLiteral(lit2);
			pushOperation(bc2);
			pushOperation(new CollectLiterals(mSharedTerm.getTerm(), bc2));
		}

	}

	public static class ConditionChain {
		final ConditionChain mPrev;
		final Term mCond;
		final boolean mNegated;

		public ConditionChain(final ConditionChain prev, final Term cond) {
			this(prev, cond, false);
		}

		public ConditionChain(final ConditionChain prev, final Term cond, final boolean negated) {
			mPrev = prev;
			mCond = cond;
			mNegated = negated;
		}

		public Term getTerm() {
			return mNegated ? mCond.getTheory().term(mCond.getTheory().mNot, mCond) : mCond;
		}

		public ConditionChain getPrevious() {
			return mPrev;
		}
	}

	private class AddTermITEAxiom implements Operation {

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
					if (at.getFunction().getName().equals("ite") && at.mTmpCtr <= Config.OCC_INLINE_TERMITE_THRESHOLD) {
						final Term c = at.getParameters()[0];
						final Term t = at.getParameters()[1];
						final Term e = at.getParameters()[2];
						mCollects.push(new CollectConditions(new ConditionChain(mConds, c), t, mIte));
						mCollects.push(new CollectConditions(new ConditionChain(mConds, c, true), e, mIte));
						return;
					}
				}
				// Not a nested ite term or a nested shared ite term
				final BuildClause bc = new BuildClause(ProofConstants.AUX_TERM_ITE);
				bc.auxAxiom(null, mTerm, mIte.getTerm(), mConds);
				pushOperation(bc);
				final SharedTerm st = getSharedTerm(mTerm);
				final EqualityProxy eqproxy = createEqualityProxy(mIte, st);
				// These asserts should be safe
				assert eqproxy != EqualityProxy.getFalseProxy();
				assert eqproxy != EqualityProxy.getTrueProxy();
				final DPLLAtom eq = eqproxy.getLiteral();
				/*
				 * We don't track merges here since there cannot be any merges on this equality. Otherwise we have an
				 * infinite term (since the termITE is a sub-term of itself).
				 */
				bc.addLiteral(eq);
				bc.getTracker().eq(mIte.getTerm(), mTerm, eq);
				ConditionChain walk = mConds;
				final Utils tmp = new Utils(bc.getTracker());
				while (walk != null) {
					pushOperation(new CollectLiterals(walk.mNegated ? walk.mCond : tmp.createNot(walk.mCond), bc));
					walk = walk.mPrev;
				}
			}
		}

		private final SharedTerm mTermITE;
		private ArrayDeque<Operation> mCollects;

		public AddTermITEAxiom(final SharedTerm termITE) {
			mTermITE = termITE;
		}

		@Override
		public void perform() {
			mCollects = new ArrayDeque<>();
			final ApplicationTerm ite = (ApplicationTerm) mTermITE.getTerm();
			final Term cond = ite.getParameters()[0];
			mCollects.push(new CollectConditions(new ConditionChain(null, cond), ite.getParameters()[1], mTermITE));
			mCollects.push(
					new CollectConditions(new ConditionChain(null, cond, true), ite.getParameters()[2], mTermITE));
			while (!mCollects.isEmpty()) {
				mCollects.pop().perform();
			}
		}
	}

	// Term creation
	public MutableAffinTerm createMutableAffinTerm(final SharedTerm term) {
		final SMTAffineTerm at = SMTAffineTerm.create(term.getTerm());
		return createMutableAffinTerm(at);
	}

	MutableAffinTerm createMutableAffinTerm(final SMTAffineTerm at) {
		final MutableAffinTerm res = new MutableAffinTerm();
		res.add(at.getConstant());
		for (final Map.Entry<Term, Rational> summand : at.getSummands().entrySet()) {
			final SharedTerm shared = getSharedTerm(summand.getKey());
			final Rational coeff = summand.getValue();
			shared.shareWithLinAr();
			res.add(shared.mFactor.mul(coeff), shared);
			res.add(shared.mOffset.mul(coeff));
		}
		return res;
	}

	public SharedTerm getSharedTerm(final Term t) {
		return getSharedTerm(t, false);
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
	public SharedTerm getSharedTerm(Term t, final boolean inCCTermBuilder) { // NOPMD
		if (t instanceof SMTAffineTerm) {
			t = ((SMTAffineTerm) t).internalize(mCompiler);
		}
		SharedTerm res = mSharedTerms.get(t);
		if (res == null) {
			// if we reach here, t is neither true nor false
			res = new SharedTerm(this, t);
			mSharedTerms.put(t, res);
			if (t instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) t;
				// Special cases
				if (t.getSort() == t.getTheory().getBooleanSort()) {
					pushOperation(new AddExcludedMiddleAxiom(res));
				} else {
					final FunctionSymbol fs = at.getFunction();
					if (fs.isInterpreted()) {
						if (fs.getName().equals("div")) {
							pushOperation(new AddDivideAxioms(t, at.getParameters()[0],
									SMTAffineTerm.create(at.getParameters()[1]).getConstant()));
						} else if (fs.getName().equals("to_int")) {
							pushOperation(new AddToIntAxioms(at));
						} else if (fs.getName().equals("ite") && fs.getReturnSort() != mTheory.getBooleanSort()) {
							pushOperation(new AddTermITEAxiom(res));
						} else if (fs.getName().equals("store")) {
							pushOperation(new AddStoreAxioms(at));
						} else if (fs.getName().equals("@diff")) {
							pushOperation(new AddDiffAxiom(at));
						}
					}
					if (needCCTerm(fs) && !inCCTermBuilder && at.getParameters().length > 0) {
						final CCTermBuilder cc = new CCTermBuilder();
						res.mCCterm = cc.convert(t);
					}
				}
			}
			if (t instanceof SMTAffineTerm) {
				res.shareWithLinAr();
			}
		}
		return res;
	}

	private static boolean needCCTerm(final FunctionSymbol fs) {
		return !fs.isInterpreted() || fs.getName() == "select" || fs.getName() == "store" || fs.getName() == "@diff";
	}

	/// Internalization stuff
	private final FormulaUnLet mUnlet = new FormulaUnLet();
	private final TermCompiler mCompiler = new TermCompiler();
	private final OccurrenceCounter mOccCounter = new OccurrenceCounter();
	private final Deque<Operation> mTodoStack = new ArrayDeque<>();
	private ProofNode mProof;

	private final Theory mTheory;
	private final DPLLEngine mEngine;
	private CClosure mCClosure;
	private LinArSolve mLASolver;
	private ArrayTheory mArrayTheory;

	private boolean mInstantiationMode;
	/**
	 * Mapping from Boolean terms to information about clauses produced for these terms.
	 */
	private final Map<Term, ClausifierInfo> mClauseData = new HashMap<>();
	/**
	 * Mapping from Boolean base terms to literals. A term is considered a base term when it corresponds to an atom or
	 * its negation.
	 */
	private final Map<Term, Literal> mLiteralData = new HashMap<>();
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
	private boolean mWarnedFailedPush = false;

	private final LogProxy mLogger;
	/**
	 * A tracker for proof production.
	 */
	private final IProofTracker mTracker;

	public Clausifier(final DPLLEngine engine, final int proofLevel) {
		mTheory = engine.getSMTTheory();
		mEngine = engine;
		mLogger = engine.getLogger();
		mTracker = proofLevel == 2 ? new ProofTracker() : new NoopProofTracker();
		mCompiler.setProofTracker(mTracker);
	}

	public void setAssignmentProduction(final boolean on) {
		mCompiler.setAssignmentProduction(on);
	}

	void pushOperation(final Operation op) {
		mTodoStack.push(op);
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
		assert !(t instanceof AnnotatedTerm);
		if (t instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) t;
			return at.getFunction() == at.getTheory().mNot ? at.getParameters()[0] : at;
		}
		// FIXME: Think about how to get Utils in here...
		// else if (t instanceof QuantifiedFormula) {
		// QuantifiedFormula qf = (QuantifiedFormula) t;
		// if (qf.getQuantifier() == QuantifiedFormula.EXISTS) {
		// // (exists (x) (phi x)) is (not (forall (x) (not (phi x))))
		// return t.getTheory().forall(qf.getVariables(),
		// Utils.createNot(qf.getSubformula()));
		// }
		// return qf;
		// }
		throw new InternalError("Unclear how to compute positive for " + t);
	}

	NamedAtom createAnonAtom(final Term smtFormula) {
		final NamedAtom atom = new NamedAtom(smtFormula, mStackLevel);
		mEngine.addAtom(atom);
		mTracker.quoted(smtFormula, atom);
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

	// QuantifiedAtom createQuantifiedAtom(Term smtFormula) {
	// String name = "quantproxy!" + numAtoms;
	// QuantifiedAtom atom = new QuantifiedAtom(name, smtFormula, m_StackLevel);
	// m_LiteralData.put(smtFormula, atom);
	// m_UndoTrail = new RemoveAtom(m_UndoTrail, smtFormula);
	// m_Engine.addAtom(atom);
	// ++numAtoms;
	// return atom;
	// }

	public EqualityProxy createEqualityProxy(final SharedTerm lhs, final SharedTerm rhs) {
		SMTAffineTerm diff = SMTAffineTerm.create(lhs.getTerm())
				.addUnchecked(SMTAffineTerm.create(rhs.getTerm()).negate(), lhs.getSort() == rhs.getSort());
		if (diff.isConstant()) {
			if (diff.getConstant().equals(Rational.ZERO)) {
				return EqualityProxy.getTrueProxy();
			}
			return EqualityProxy.getFalseProxy();
		}
		diff = diff.div(diff.getGcd());
		// normalize equality to integer logic if all variables are integer.
		if (mTheory.getLogic().isIRA() && !diff.isIntegral() && diff.isAllIntSummands()) {
			diff = diff.typecast(getTheory().getSort("Int"));
		}
		// check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
		if (diff.isIntegral() && !diff.getConstant().isIntegral()) {
			return EqualityProxy.getFalseProxy();
		}
		// we cannot really normalize the sign of the term. Try both signs.
		EqualityProxy eqForm = mEqualities.get(diff);
		if (eqForm != null) {
			return eqForm;
		}
		eqForm = mEqualities.get(diff.negate());
		if (eqForm != null) {
			return eqForm;
		}
		eqForm = new EqualityProxy(this, lhs, rhs);
		mEqualities.put(diff, eqForm);
		return eqForm;
	}

	Literal getLiteralForPolarity(final Term t, final boolean positive) {
		assert t == toPositive(t);
		final ClausifierInfo ci = mClauseData.get(t);
		if (ci != null && ci.getLiteral() != null) {
			if (positive) {
				if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED)) {
					pushOperation(new AddAuxAxioms(t, ci.getLiteral(), positive));
				}
				return ci.getLiteral();
			}
			if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED)) {
				pushOperation(new AddAuxAxioms(t, ci.getLiteral(), positive));
			}
			return ci.getLiteral().negate();
		}
		return null;
	}

	Literal getLiteral(final Term t) {
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
			pushOperation(new AddAuxAxioms(idx, lit, pos));
			return pos ? lit : lit.negate();
		}
		if (pos) {
			if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED)) {
				pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), true));
			}
			return ci.getLiteral();
		}
		if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED)) {
			pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), false));
		}
		return ci.getLiteral().negate();
	}

	Literal getLiteralTseitin(final Term t) {
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
			pushOperation(new AddAuxAxioms(idx, lit, true));
			pushOperation(new AddAuxAxioms(idx, lit, false));
			return pos ? lit : lit.negate();
		}
		if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED)) {
			pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), true));
		}
		if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED)) {
			pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), false));
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
			final Literal[] lits = new Literal[] {
					mCClosure.createCCEquality(mStackLevel, mSharedTrue.mCCterm, mSharedFalse.mCCterm).negate() };
			mEngine.addFormulaClause(lits, getProofNewSource(ProofConstants.AUX_TRUE_NOT_FALSE,
					mTracker.auxAxiom(ProofConstants.AUX_TRUE_NOT_FALSE, lits[0], mTheory.mTrue, null, null)));
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
	// private void setupQuantifiers() {
	// TODO Implement
	// setupCClosure();
	// try {
	// Class<?> pcclass = getClass().getClassLoader().loadClass(
	// System.getProperty(
	// Config.PATTERNCOMPILER,
	// Config.DEFAULT_PATTERNCOMPILER));
	// patternCompiler = (IPatternCompiler)pcclass.newInstance();
	// } catch (Exception e) {
	// logger.fatal("Could not load Pattern Compiler",e);
	// throw new RuntimeException("Could not load Pattern Compiler",e);
	// }
	// quantTheory = new QuantifierTheory(cclosure);
	// dpllEngine.addTheory(quantTheory);
	// }

	public void setLogic(final Logics logic) {
		if (mEngine.isProofGenerationEnabled()) {
			setSourceAnnotation(LeafNode.NO_THEORY, SourceAnnotation.EMPTY_SOURCE_ANNOT);
		}

		if (logic.isBitVector() || logic.isQuantified() || logic.isNonLinearArithmetic()) {
			throw new UnsupportedOperationException("Logic " + logic.toString() + " unsupported");
		}

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
		if (mEngine.isProofGenerationEnabled()) {
			setSourceAnnotation(LeafNode.NO_THEORY, SourceAnnotation.EMPTY_SOURCE_ANNOT);
			if (f instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) f;
				final Annotation[] annots = at.getAnnotations();
				for (final Annotation a : annots) {
					if (a.getKey().equals(":named")) {
						final String name = ((String) a.getValue()).intern();
						setSourceAnnotation(LeafNode.NO_THEORY, new SourceAnnotation(name, null));
						break;
					}
				}
			}
		}
		Term tmp = mUnlet.unlet(f);
		// f = null;
		// System.err.println(tmp.toStringDirect());
		Term tmp2;
		try {
			tmp2 = mCompiler.transform(tmp);
		} finally {
			mCompiler.reset();
		}
		tmp = null;
		// System.err.println("Transformed");
		// System.err.println(SMTAffineTerm.cleanup(tmp2).toStringDirect());
		final Term proof = mTracker.getRewriteProof(f);
		mTracker.reset();

		mOccCounter.count(tmp2);
		final Map<Term, Set<String>> names = mCompiler.getNames();
		if (names != null) {
			for (final Map.Entry<Term, Set<String>> me : names.entrySet()) {
				trackAssignment(me.getKey(), me.getValue());
			}
		}
		// System.err.println("Started convertion");
		pushOperation(new AddAsAxiom(tmp2, proof));
		mInstantiationMode = false;
		run();
		// System.err.println("Ended convertion");
		mOccCounter.reset(tmp2);
		tmp2 = null;

		// logger.info("Added " + numClauses + " clauses, " + numAtoms
		// + " auxiliary atoms.");
		if (mEngine.isProofGenerationEnabled()) {
			setSourceAnnotation(LeafNode.NO_THEORY, SourceAnnotation.EMPTY_SOURCE_ANNOT);
		}
	}

	// TODO need an instantiation mode here to add clauses to DPLL as deletable instantiations
	// public void addInstantiation(Term f, Map<TermVariable, Term> inst,
	// Literal quantproxy) {
	// if (m_Engine.isProofGenerationEnabled()) {
	// // TODO
	// }
	// m_Unlet.beginScope();
	// m_Unlet.addSubstitutions(inst);
	// Term tmp = m_Unlet.unlet(f);
	// m_Unlet.endScope();
	// Term tmp2 = m_Compiler.transform(tmp);
	//
	// /*
	// * This is an ugly hack. Since operations might introduce proxy
	// * literals with definitions that might be deleted once an instantiation
	// * is deleted, we cannot permanently store the proxy literals and the
	// * knowledge about their aux axioms.
	// */
	// pushUndoTrail();
	// m_InstantiationMode = true;
	// if (quantproxy == null) {
	// // toplevel match
	// pushOperation(new AddAsAxiom(tmp2));
	// } else {
	// BuildClause bc = new BuildClause(LeafNode.QUANT_INST);
	// bc.addLiteral(quantproxy.negate());
	// pushOperation(new CollectLiterals(tmp2, bc));
	// }
	// run();
	// popUndoTrail();
	//
	// if (m_Engine.isProofGenerationEnabled()) {
	// // TODO
	// }
	// }

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

	public void setSourceAnnotation(final int leafKind, final IAnnotation sourceAnnot) {
		mProof = new LeafNode(leafKind, sourceAnnot);
	}

	private ProofNode getProofNewSource(final Term source) {
		return getProofNewSource(LeafNode.NO_THEORY, source);
	}

	private ProofNode getProofNewSource(final int leafKind, final Term source) {
		if (source == null) {
			return mProof;
		}
		if (mProof instanceof LeafNode) {
			final LeafNode ln = (LeafNode) mProof;
			final SourceAnnotation annot = new SourceAnnotation((SourceAnnotation) ln.getTheoryAnnotation(), source);
			return new LeafNode(leafKind, annot);
		}
		return mProof;
	}

	private ProofNode getClauseProof(Term proofTerm) {
		proofTerm = mTracker.clause(proofTerm);
		return getProofNewSource(proofTerm);
	}

	public IAnnotation getAnnotation() {
		if (mProof instanceof LeafNode) {
			return ((LeafNode) mProof).getTheoryAnnotation();
		}
		return null;
	}

	public Theory getTheory() {
		return mTheory;
	}

	private void trackAssignment(final Term term, final Set<String> names) {
		Literal lit;
		final Term idx = toPositive(term);
		final boolean pos = idx == term;
		if (idx instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) idx;
			final FunctionSymbol fs = at.getFunction();
			if (fs.getName().equals("<=")) {
				lit = createLeq0(at);
			} else if (fs.getName().equals("=") && at.getParameters()[0].getSort() != mTheory.getBooleanSort()) {
				final SharedTerm lhs = getSharedTerm(at.getParameters()[0]);
				final SharedTerm rhs = getSharedTerm(at.getParameters()[1]);
				final EqualityProxy ep = createEqualityProxy(lhs, rhs);
				if (ep == EqualityProxy.getTrueProxy()) {
					lit = new DPLLAtom.TrueAtom();
				} else if (ep == EqualityProxy.getFalseProxy()) {
					lit = new DPLLAtom.TrueAtom().negate();
				} else {
					lit = ep.getLiteral();
				}
			} else if ((!fs.isIntern() || fs.getName().equals("select"))
					&& fs.getReturnSort() == mTheory.getBooleanSort()) {
				lit = createBooleanLit(at);
			} else if (at == mTheory.mTrue) {
				lit = new DPLLAtom.TrueAtom();
			} else if (at == mTheory.mFalse) {
				lit = new DPLLAtom.TrueAtom().negate();
			} else {
				lit = getLiteralTseitin(idx);
			}
		} else {
			lit = getLiteralTseitin(idx);
		}
		if (!pos) {
			lit = lit.negate();
		}
		for (final String name : names) {
			mEngine.trackAssignment(name, lit);
		}
	}

	private Literal createLeq0(final ApplicationTerm leq0term) {
		Literal lit = mLiteralData.get(leq0term);
		if (lit == null) {
			final SMTAffineTerm sum = SMTAffineTerm.create(leq0term.getParameters()[0]);
			final MutableAffinTerm msum = createMutableAffinTerm(sum);
			lit = mLASolver.generateConstraint(msum, false, mStackLevel);
			mLiteralData.put(leq0term, lit);
			mUndoTrail = new RemoveAtom(mUndoTrail, leq0term);
		}
		return lit;
	}

	private Literal createBooleanLit(final ApplicationTerm term) {
		Literal lit = mLiteralData.get(term);
		if (lit == null) {
			if (term.getParameters().length == 0) {
				lit = createBooleanVar(term);
			} else {
				final SharedTerm st = getSharedTerm(term);
				final EqualityProxy eq = createEqualityProxy(st, mSharedTrue);
				// Safe since m_Term is neither true nor false
				assert eq != EqualityProxy.getTrueProxy();
				assert eq != EqualityProxy.getFalseProxy();
				lit = eq.getLiteral();
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

	public Literal getCreateLiteral(final Term f) {
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
			res = createBooleanLit(at);
		} else if (at == mTheory.mTrue) {
			res = new TrueAtom();
		} else if (at == mTheory.mFalse) {
			res = new TrueAtom().negate();
		} else if (fs.getName().equals("=")) {
			if (at.getParameters()[0].getSort() == mTheory.getBooleanSort()) {
				res = getLiteralTseitin(at);
			} else {
				final EqualityProxy ep =
						createEqualityProxy(getSharedTerm(at.getParameters()[0]), getSharedTerm(at.getParameters()[1]));
				if (ep == EqualityProxy.getFalseProxy()) {
					res = new TrueAtom().negate();
				} else if (ep == EqualityProxy.getTrueProxy()) {
					res = new TrueAtom();
				} else {
					res = ep.getLiteral();
				}
			}
		} else if (fs.getName().equals("<=")) {
			res = createLeq0(at);
		} else {
			res = getLiteralTseitin(at);
		}

		mInstantiationMode = false;
		run();
		mOccCounter.reset(tmp2);
		tmp2 = null;
		return negated ? res.negate() : res;
	}

	public static boolean shouldFlatten(final ApplicationTerm term) {
		return term.getFunction() == term.getTheory().mOr && term.mTmpCtr <= Config.OCC_INLINE_THRESHOLD;
	}

}
