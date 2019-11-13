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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTermPairHash.Info.Entry;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.EQAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayQueue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class CClosure implements ITheory {
	final DPLLEngine mEngine;
	final Map<Term, CCTerm> mAnonTerms = new HashMap<>();
	final ArrayList<CCTerm> mAllTerms = new ArrayList<>();
	final CCTermPairHash mPairHash = new CCTermPairHash();
	final ArrayQueue<Literal> mPendingLits = new ArrayQueue<>();
	final ScopedHashMap<Object, CCBaseTerm> mSymbolicTerms =
			new ScopedHashMap<>();
	int mNumFunctionPositions;
	int mMergeDepth;
	final ArrayDeque<CCTerm> mMerges = new ArrayDeque<>();
	final ArrayDeque<SymmetricPair<CCAppTerm>> mPendingCongruences =
		new ArrayDeque<>();

	private long mInvertEdgeTime, mEqTime, mCcTime, mSetRepTime;
	private long mCcCount, mMergeCount;

	private int mStoreNum, mSelectNum, mDiffNum;

	public CClosure(final DPLLEngine engine) {
		mEngine = engine;
	}

	public CCTerm createAnonTerm(final SharedTerm flat) {
		final CCTerm term = new CCBaseTerm(false, mNumFunctionPositions, flat, flat);
		mAnonTerms.put(flat.getTerm(), term);
		mAllTerms.add(term);
		return term;
	}

	/**
	 * Searches for the congruent term of {@code CCAppTerm(func,arg)} that would have been merged on the lowest decision
	 * level.
	 *
	 * @param func
	 *            A term on the path from this.mFunc to this.mFunc.mRepStar.
	 * @param arg
	 *            A term on the path from this.mArg to this.mArg.mRepStar.
	 * @return The congruent CCAppTerm or null if there is no congruent application.
	 */
	private CCAppTerm findCongruentAppTerm(CCTerm func, CCTerm arg) {
		final CCParentInfo argInfo = arg.getRepresentative().mCCPars.getInfo(func.mParentPosition);
		int congruenceLevel = Integer.MAX_VALUE;
		CCAppTerm congruentTerm = null;
		// Look for all congruent terms for the argument.
		for (final Parent p : argInfo.mCCParents) {
			CCAppTerm papp = p.getData();
			CCTerm pfunc = papp.getFunc();
			CCTerm parg = papp.getArg();
			if (pfunc.getRepresentative() != func.getRepresentative()) {
				// this term is not congruent
				continue;
			}
			if (pfunc == func && parg == arg) {
				// this is the app term for which we search a congruent term; skip it
				continue;
			}
			// compute the level where the congruence occurred
			int level = Math.max(getDecideLevelForPath(pfunc, func), getDecideLevelForPath(parg, arg));
			// store the congruence with the smallest level
			if (level < congruenceLevel) {
				congruenceLevel = level;
				congruentTerm = papp;
			}
		}
		return congruentTerm;
	}

	public CCAppTerm createAppTerm(final boolean isFunc, final CCTerm func, final CCTerm arg) {
		assert func.mIsFunc;
		final CCParentInfo info = arg.mRepStar.mCCPars.getExistingParentInfo(func.mParentPosition);
		if (info != null) {
			final SimpleList<CCAppTerm.Parent> prevParents = info.mCCParents;
			assert prevParents.wellformed();
			for (final CCAppTerm.Parent termpar : prevParents) {
				final CCAppTerm term = termpar.getData();
				if (term.mFunc == func && term.mArg == arg) {
					return term;
				}
			}
		}
		final CCAppTerm term = new CCAppTerm(isFunc,
				isFunc ? func.mParentPosition + 1 : 0, func, arg, null, this);
		term.addParentInfo(this);
		final CCAppTerm congruentTerm = findCongruentAppTerm(func, arg);
		mEngine.getLogger().debug("createAppTerm %s congruent: %s", term, congruentTerm);
		if (congruentTerm != null) {
			// Here, we do not have the resulting term in the equivalence class
			// Mark pending congruence
			addPendingCongruence(term, congruentTerm);
		}

		if (!isFunc) {
			/* if this created a complete application term, activate corresponding triggers */
			CCTerm partialApp = term;
			while (partialApp instanceof CCAppTerm) {
				CCAppTerm app = (CCAppTerm) partialApp;
				CCTerm appArg = app.getArg();
				/* E-Matching: activate reverse trigger */
				int parentpos = app.getFunc().mParentPosition;
				final CCParentInfo argInfo = appArg.mCCPars.getInfo(parentpos);
				if (argInfo != null) {
					for (final ReverseTrigger trigger : argInfo.mReverseTriggers) {
						trigger.activate(term);
					}
				}
				partialApp = app.getFunc();
			}
			/* E-Matching: activate find trigger */
			{
				final CCParentInfo funcInfo = partialApp.mCCPars.getInfo(0);
				if (funcInfo != null) {
					for (final ReverseTrigger trigger : funcInfo.mReverseTriggers) {
						trigger.activate(term);
					}
				}
			}
		}
		return term;
	}

	// Only works for non-polymorphic function symbols
	private CCTerm convertFuncTerm(final FunctionSymbol sym, final CCTerm[] args, final int numArgs) {
		if (numArgs == 0) {
			CCBaseTerm term = mSymbolicTerms.get(sym);
			if (term == null) {
				term = new CCBaseTerm(args.length > 0, mNumFunctionPositions, sym, null);
				mNumFunctionPositions += args.length;
				mSymbolicTerms.put(sym, term);
			}
			return term;
		} else {
			final CCTerm pred = convertFuncTerm(sym, args, numArgs - 1);
			final CCAppTerm appTerm = createAppTerm(numArgs < args.length, pred, args[numArgs - 1]);
			return appTerm;
		}
	}

	/**
	 * Function to retrieve the CCTerm representing a function symbol.
	 * @param sym Function symbol.
	 * @return CCTerm representing this function symbol in the egraph.
	 */
	public CCTerm getFuncTerm(final FunctionSymbol sym) {
		CCBaseTerm term = mSymbolicTerms.get(sym);
		if (term == null) {
			term = mSymbolicTerms.get(sym.getName());
			if (term == null) {
				term = new CCBaseTerm(sym.getParameterSorts().length > 0,
						mNumFunctionPositions, sym, null);
				mNumFunctionPositions += sym.getParameterSorts().length;
			} else {
				// This is a polymorphic function symbol
				term = new CCBaseTerm(
						term.mIsFunc, term.mParentPosition, sym, null);
			}
			mSymbolicTerms.put(sym, term);
		}
		return term;
	}

	/**
	 * Get all terms that appear under a given function at a given position.
	 *
	 * @param sym
	 *            the function symbol
	 * @param argPos
	 *            the argument position
	 * @return the CCTerms that appear under the given function as argPos-th argument.
	 */
	public Collection<CCTerm> getArgTermsForFunc(final FunctionSymbol sym, final int argPos) {
		assert sym.getParameterSorts().length > argPos;
		final List<CCTerm> args = new ArrayList<>();
		List<CCTerm> parents = new ArrayList<>();
		parents.add(getFuncTerm(sym));
		for (int i = 0; i <= argPos; i++) {
			parents = getApplications(parents);
		}
		// Collect the arguments at argPos
		for (final CCTerm par : parents) {
			assert par instanceof CCAppTerm;
			args.add(((CCAppTerm) par).getArg());
		}
		return args;
	}

	/**
	 * Get all terms that are a (complete) function application of the given function symbol.
	 *
	 * @param sym
	 *            the function symbol.
	 * @return all function applications of the given function symbol.
	 */
	public List<CCTerm> getAllFuncApps(final FunctionSymbol sym) {
		List<CCTerm> parents = Collections.singletonList(getFuncTerm(sym));
		for (int i = 0; i < sym.getParameterSorts().length; i++) {
			parents = getApplications(parents);
		}
		return parents;
	}

	/**
	 * Get all applications given partial functions.
	 *
	 * @param partialFunctions
	 *            CCTerms that are partial functions.
	 * @return all CCTerms that are applications of the given partial functions.
	 */
	static List<CCTerm> getApplications(final List<CCTerm> partialFunctions) {
		final List<CCTerm> applications = new ArrayList<>();
		for (final CCTerm funcTerm : partialFunctions) {
			final CCParentInfo info = funcTerm.getRepresentative().mCCPars.getInfo(0);
			if (info != null) {
				for (final Parent grandparent : info.mCCParents) {
					applications.add(grandparent.getData());
				}
			}
		}
		return applications;
	}

	/**
	 * Get all (complete) function applications of a given function symbol with a given argument at a given
	 * position.
	 *
	 * @param sym
	 *            the function symbol.
	 * @param arg
	 *            the argument the application term should contain.
	 * @param argPos
	 *            the position of the given argument.
	 * @return all function applications of the given function symbol with the given argument at the given position.
	 */
	public List<CCTerm> getAllFuncAppsForArg(final FunctionSymbol sym, final CCTerm arg, final int argPos) {
		final CCTerm funcTerm = getFuncTerm(sym);
		final int parentPosition = funcTerm.mParentPosition + argPos;
		final CCParentInfo info = arg.getRepresentative().mCCPars.getInfo(parentPosition);

		List<CCTerm> funcApps = new ArrayList<>();
		for (final Parent parent : info.mCCParents) {
			if (!parent.isMarked()) {
				funcApps.add(parent.getData());
			}
		}
		for (int i = argPos + 1; i < sym.getParameterSorts().length; i++) {
			funcApps = getApplications(funcApps);
		}
		return funcApps;
	}

	/**
	 * Insert a Compare trigger that will be activated as soon as the two given CCTerms are equal. It is inserted into
	 * the pair hash tables and all intermediate pair infos.
	 *
	 * @param t1
	 *            the first CCTerm.
	 * @param t2
	 *            the second CCTerm.
	 * @param trigger
	 *            the Compare trigger.
	 */
	public void insertCompareTrigger(CCTerm t1, CCTerm t2, final CompareTrigger trigger) {
		assert t1.getRepresentative() != t2.getRepresentative();
		assert !trigger.inList();
		while (true) {
			// make t1 the term that was merged before t2 was merged.
			if (t1.mMergeTime > t2.mMergeTime) {
				final CCTerm tmp = t1;
				t1 = t2;
				t2 = tmp;
			}

			// if t1 is its own representative, then t2 should also be the representative because of merge time
			if (t1.mRep == t1) {
				assert t2.mRep == t2;
				// Insert this entry into the pair hash, create it if necessary.
				CCTermPairHash.Info info = mPairHash.getInfo(t1, t2);
				if (info == null) {
					info = new CCTermPairHash.Info(t1, t2);
					mPairHash.add(info);
				}
				info.mCompareTriggers.prependIntoJoined(trigger, true);
				break;
			}

			// find the pair info entry in the pair info list of t1 or create a new one.
			assert t1.mRep != t2;
			boolean found = false;
			for (final CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
				// assert (!info.eqlits.isEmpty());
				if (pentry.mOther == t2) {
					info.mCompareTriggers.prependIntoJoined(trigger, false);
					found = true;
					break;
				}
			}
			if (!found) {
				// we need to create a new entry.
				final CCTermPairHash.Info info = new CCTermPairHash.Info(t1, t2);
				info.mRhsEntry.unlink();
				info.mCompareTriggers.prependIntoJoined(trigger, false);
			}
			t1 = t1.mRep;
		}
	}

	/**
	 * Remove a given Compare trigger.
	 */
	public void removeCompareTrigger(final CompareTrigger trigger) {
		CCTerm t1 = trigger.getLhs();
		CCTerm t2 = trigger.getRhs();
		while (true) {
			// make t1 the term that was merged before t2 was merged.
			if (t1.mMergeTime > t2.mMergeTime) {
				final CCTerm tmp = t1;
				t1 = t2;
				t2 = tmp;
			}

			// if t1 is its own representative, then t2 should also be the representative because of merge time
			if (t1.mRep == t1) {
				assert t2.mRep == t2;
				// Insert this entry into the pair hash, create it if necessary.
				CCTermPairHash.Info info = mPairHash.getInfo(t1, t2);
				assert info != null;
				info.mCompareTriggers.undoPrependIntoJoined(trigger, true);
				break;
			}

			// find the pair info entry in the pair info list of t1 or create a new one.
			// isLast is set if t1 was merged with t2; in this case the equality entry lists were not joined.
			assert t1.mRep != t2;
			boolean found = false;
			for (final CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
				// assert (!info.eqlits.isEmpty());
				if (pentry.mOther == t2) {
					info.mCompareTriggers.undoPrependIntoJoined(trigger, false);
					found = true;
					break;
				}
			}
			assert found;
			t1 = t1.mRep;
		}
	}

	/**
	 * Insert a Reverse trigger that will be activated as soon as a new function application of the given function
	 * symbol with a given argument at a given position exists.
	 *
	 * @param fSym
	 *            the function symbol.
	 * @param arg
	 *            the argument the new term should contain.
	 * @param argPos
	 *            the position of this argument.
	 * @param trigger
	 *            the Reverse trigger.
	 */
	public void insertReverseTrigger(final FunctionSymbol sym, CCTerm arg, final int argPos,
			final ReverseTrigger trigger) {
		final CCTerm func = getFuncTerm(sym);
		final int parentPos = func.mParentPosition + argPos;
		while (arg != arg.mRep) {
			final CCParentInfo info = arg.mCCPars.createInfo(parentPos);
			info.mReverseTriggers.prependIntoJoined(trigger, false);
			arg = arg.mRep;
		}
		final CCParentInfo info = arg.mCCPars.createInfo(parentPos);
		info.mReverseTriggers.prependIntoJoined(trigger, true);
	}

	/**
	 * Insert a Reverse trigger that will be activated as soon as a new function application of the given function
	 * symbol exists.
	 *
	 * @param fSym
	 *            the function symbol.
	 * @param trigger
	 *            the Reverse trigger.
	 */
	public void insertReverseTrigger(final FunctionSymbol sym, final ReverseTrigger trigger) {
		final CCTerm func = getFuncTerm(sym);
		final CCParentInfo info = func.mCCPars.createInfo(0);
		info.mReverseTriggers.append(trigger);
	}

	/**
	 * Remove a given Reverse trigger.
	 */
	public void removeReverseTrigger(final ReverseTrigger trigger) {
		final CCTerm func = getFuncTerm(trigger.getFunctionSymbol());
		CCTerm termWithTrigger;
		final int parentPos;
		if (trigger.getArgPosition() < 0) {
			/* this is a find trigger */
			assert func == func.mRep;
			termWithTrigger = func;
			parentPos = 0;
		} else {
			/* this is a reverse trigger */
			termWithTrigger = trigger.getArgument();
			parentPos = func.mParentPosition + trigger.getArgPosition();
		}
		while (termWithTrigger != termWithTrigger.mRep) {
			final CCParentInfo info = termWithTrigger.mCCPars.createInfo(parentPos);
			info.mReverseTriggers.undoPrependIntoJoined(trigger, false);
			termWithTrigger = termWithTrigger.mRep;
		}
		final CCParentInfo info = termWithTrigger.mCCPars.createInfo(parentPos);
		info.mReverseTriggers.undoPrependIntoJoined(trigger, true);
	}

	/**
	 * Find the representative CCTerm for the given term. This function does not create new terms. If there is no
	 * equivalent CCTerm, it returns null. If a term that is congruent to the given term already exists, it will return
	 * the representative of this congruent term.
	 *
	 * @param term
	 *            The term which a representative is searched for.
	 * @return The representative, or null if no congruent term exists in the CClosure.
	 */
	public CCTerm getCCTermRep(final Term term) {
		if (mAnonTerms.containsKey(term)) {
			return mAnonTerms.get(term).getRepresentative();
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			CCTerm func = getFuncTerm(at.getFunction()).getRepresentative();
			for (final Term argTerm : at.getParameters()) {
				final CCTerm arg = getCCTermRep(argTerm);
				if (arg == null) {
					return null;
				}
				func = findCCAppTermRep(func, arg);
				if (func == null) {
					return null;
				}
			}
			return func;
		}
		return null;
	}

	/**
	 * Find the representative CCTerm for the application of funcRep and argRep. This function does not create new
	 * terms. If there is no equivalent CCTerm it returns null. If a term that is congruent to the given term already
	 * exists it will return the representative of this congruent term.
	 *
	 * @param funcRep
	 *            the representative of the partial function application term.
	 * @param argRep
	 *            the representative of the argument term.
	 * @return The representative of the application, or null if no congruent term exists in the CClosure.
	 */
	private CCTerm findCCAppTermRep(final CCTerm funcRep, final CCTerm argRep) {
		final CCParentInfo info = funcRep.mCCPars.getInfo(0);
		if (info == null) {
			return null;
		}
		for (final Parent parent : info.mCCParents) {
			if (parent.getData().getArg().getRepresentative() == argRep) {
				return parent.getData().getRepresentative();
			}
		}
		return null;
	}

	/**
	 * For two given CCTerms, check if the equality is set.
	 *
	 * @return true if the terms are in the same congruence class, false otherwise.
	 */
	public boolean isEqSet(final CCTerm first, final CCTerm second) {
		final CCTerm firstRep = first.getRepresentative();
		final CCTerm secondRep = second.getRepresentative();
		if (firstRep == secondRep) {
			return true;
		}
		return false;
	}

	/**
	 * For two given CCTerms, check if the disequality is set.
	 *
	 * @return true if the disequality is set, false otherwise.
	 */
	public boolean isDiseqSet(final CCTerm first, final CCTerm second) {
		final CCTerm firstRep = first.getRepresentative();
		final CCTerm secondRep = second.getRepresentative();
		final CCTermPairHash.Info diseqInfo = mPairHash.getInfo(firstRep, secondRep);
		if (diseqInfo != null && diseqInfo.mDiseq != null) {
			return true;
		}
		return false;
	}

	/**
	 * Insert an equality entry into the pair hash table and all pair infos of the intermediate representatives.
	 * 
	 * @param t1
	 *            one side of the equality.
	 * @param t2
	 *            the other side of the equality
	 * @param eqentry
	 *            the equality entry that should be inserted into the pair infos.
	 */
	public void insertEqualityEntry(CCTerm t1, CCTerm t2, final CCEquality.Entry eqentry) {
		while (true) {
			// make t1 the term that was merged before t2 was merged.
			if (t1.mMergeTime > t2.mMergeTime) {
				final CCTerm tmp = t1;
				t1 = t2;
				t2 = tmp;
			}

			// if t1 is its own representative, then t2 should also be the representative because of merge time
			if (t1.mRep == t1) {
				assert t2.mRep == t2;
				// Insert this entry into the pair hash, create it if necessary.
				CCTermPairHash.Info info = mPairHash.getInfo(t1, t2);
				if (info == null) {
					info = new CCTermPairHash.Info(t1, t2);
					mPairHash.add(info);
				}
				info.mEqlits.prependIntoJoined(eqentry, true);
				break;
			}

			// find the pair info entry in the pair info list of t1 or create a new one.
			// isLast is set if t1 was merged with t2; in this case the equality entry lists were not joined.
			final boolean isLast = t1.mRep == t2;
			boolean found = false;
			for (final CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
				// assert (!info.eqlits.isEmpty());
				if (pentry.mOther == t2) {
					info.mEqlits.prependIntoJoined(eqentry, isLast);
					found = true;
					break;
				}
			}
			if (!found) {
				// we need to create a new entry.
				final CCTermPairHash.Info info = new CCTermPairHash.Info(t1, t2);
				info.mRhsEntry.unlink();
				info.mEqlits.prependIntoJoined(eqentry, isLast);
			}
			if (isLast) {
				break;
			}
			t1 = t1.mRep;
		}
	}

	public CCEquality createCCEquality(final int stackLevel, final CCTerm t1, final CCTerm t2) {
		assert (t1 != t2);
		CCEquality eq = null;
		assert t1.invariant();
		assert t2.invariant();

		eq = new CCEquality(stackLevel, t1, t2);
		insertEqualityEntry(t1, t2, eq.getEntry());
		mEngine.addAtom(eq);

		assert t1.invariant();
		assert t2.invariant();
		assert t1.pairHashValid(this);
		assert t2.pairHashValid(this);

		if (t1.mRepStar == t2.mRepStar) {
			if (mEngine.getLogger().isDebugEnabled()) {
				mEngine.getLogger().debug("CC-Prop: " + eq + " repStar: " + t1.mRepStar);
			}
			mPendingLits.add(eq);
		} else {
			final CCEquality diseq = mPairHash.getInfo(t1.mRepStar, t2.mRepStar).mDiseq;
			if (diseq != null) {
				if (mEngine.getLogger().isDebugEnabled()) {
					mEngine.getLogger().debug("CC-Prop: " + eq.negate() + " diseq: " + diseq);
				}
				eq.mDiseqReason = diseq;
				mPendingLits.add(eq.negate());
			}
		}
		return eq;
	}

	/// Only works for non-polymorphic function symbols.
	public boolean knowsConstant(final FunctionSymbol sym) {
		return mSymbolicTerms.containsKey(sym);
	}

	// TODO: Obsolete function; only used by tests
	@Deprecated
	public CCTerm createFuncTerm(
			final FunctionSymbol sym, final CCTerm[] subterms, final SharedTerm fapp) {
		final CCTerm term = convertFuncTerm(sym, subterms, subterms.length);
		if (term.mFlatTerm == null) {
			mAllTerms.add(term);
		}
		term.mFlatTerm = fapp;
		return term;
	}

	public void addTerm(final CCTerm term, final SharedTerm shared) {
		term.mFlatTerm = shared;
		mAllTerms.add(term);
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		if (!(literal.getAtom() instanceof CCEquality)) {
			return;
		}
		final CCEquality eq = (CCEquality) literal.getAtom();
		if (eq.mStackDepth != -1) {
			backtrackStack(eq.mStackDepth);
			eq.mStackDepth = -1;
			if (literal != eq) {
				undoSep(eq);
			}
		}
	}

	@Override
	public Clause computeConflictClause() {
		Clause res = checkpoint();
		if (res == null) {
			res = checkpoint();
		}
		assert mPendingCongruences.isEmpty();
		return res;
	}

	@Override
	public Literal getPropagatedLiteral() {
		final Literal lit = mPendingLits.poll();
		assert (lit == null || checkPending(lit));
		return lit;
	}

	@Override
	public Clause getUnitClause(final Literal lit) {
		if (lit.getAtom() instanceof LAEquality) {
			final LAEquality laeq = (LAEquality) lit.getAtom();
			for (final CCEquality eq : laeq.getDependentEqualities()) {
				if (eq.getStackPosition() >= 0
					&& eq.getStackPosition() < laeq.getStackPosition()
						&& eq.getDecideStatus().getSign() == lit.getSign()) {
					return new Clause(new Literal[] {
					     eq.getDecideStatus().negate(), lit },
							new LeafNode(LeafNode.EQ, EQAnnotation.EQ));
				}
			}
			throw new AssertionError("Cannot find explanation for " + laeq);
		} else if (lit instanceof CCEquality) {
			final CCEquality eq = (CCEquality) lit;
			return computeCycle(eq);
		} else {
			/* ComputeAntiCycle */
			final CCEquality eq = (CCEquality) lit.negate();
			return computeAntiCycle(eq);
		}
	}

	@Override
	public int checkCompleteness() {
		return DPLLEngine.COMPLETE;
	}

	@Override
	public Clause setLiteral(final Literal literal) {
		if (!(literal.getAtom() instanceof CCEquality)) {
			return null;
		}
		final CCEquality eq = (CCEquality) literal.getAtom();
		final LAEquality laeq = eq.getLASharedData();
		if (laeq != null) {
			assert ((List<CCEquality>) laeq.getDependentEqualities()).contains(eq);
			if (laeq.getDecideStatus() != null
				&& laeq.getDecideStatus().getSign() != literal.getSign()) {
				return new Clause(new Literal[] {
					laeq.getDecideStatus().negate(), literal.negate() },
						new LeafNode(LeafNode.EQ, EQAnnotation.EQ));
			}
			mPendingLits.add(literal == eq ? laeq : laeq.negate());
		}
		if (literal == eq) {
			if (eq.getLhs().mRepStar != eq.getRhs().mRepStar) {
				eq.mStackDepth = mMerges.size();
				final Clause conflict = eq.getLhs().merge(this, eq.getRhs(), eq);
				if (conflict != null) {
					return conflict;
				}
			}
		} else {
			final CCTerm left = eq.getLhs().mRepStar;
			final CCTerm right = eq.getRhs().mRepStar;

			/* Check for conflict */
			if (left == right) {
				final Clause conflict = computeCycle(eq);
				if (conflict != null) {
					return conflict;
				}
			}
			separate(left, right, eq);
			eq.mStackDepth = mMerges.size();
		}
		return null;
	}

	private CCTermPairHash.Info mLastInfo;

	private void separate(final CCTerm lhs, final CCTerm rhs, final CCEquality atom) {
		if (mLastInfo == null || !mLastInfo.equals(lhs, rhs)) {
			mLastInfo = mPairHash.getInfo(lhs, rhs);
			assert mLastInfo != null;
		}
		if (mLastInfo.mDiseq != null) {
			return;
		}

		mLastInfo.mDiseq = atom;
		/* Propagate inequalities */
		for (final CCEquality.Entry eqentry : mLastInfo.mEqlits) {
			final CCEquality eq = eqentry.getCCEquality();
			if (eq.getDecideStatus() == null) {
				eq.mDiseqReason = atom;
				addPending(eq.negate());
			}
		}
		/* reverse congruence closure
		for (CCTerm t1 : members) {
			if (t1 instanceof CCAppTerm) {
				CCAppTerm app1 = (CCAppTerm) t1;
				for (CCTerm t2 : members) {
					if (t2 instanceof CCAppTerm) {
						CCAppTerm app2 = (CCAppTerm) t2;
						if (app1.func.rep == app2.func.rep
							&& !app1.arg.rep.inDiseq(app2.arg.rep.diseq)) {
							separate(app1.arg.rep, app2.arg.rep, atom);
						} else if (app1.arg.rep == app2.arg.rep
								   && !app1.func.rep.inDiseq(app2.func.rep.diseq)) {
							separate(app1.func.rep, app2.func.rep, atom);
						}
					}
				}
			}
		} */
	}

	private void undoSep(final CCEquality atom) {
		atom.mDiseqReason = null;
		CCTermPairHash.Info destInfo = mPairHash.getInfo(
				atom.getLhs().mRepStar, atom.getRhs().mRepStar);
		if (destInfo != null && destInfo.mDiseq != null) {
			destInfo = mPairHash.getInfo(
					atom.getLhs().mRepStar, atom.getRhs().mRepStar);
			if (destInfo.mDiseq == atom) {
				destInfo.mDiseq = null;
			}
		}
	}

	public Clause computeCycle(final CCEquality eq) {
		final CongruencePath congPath = new CongruencePath(this);
		final Clause res = congPath.computeCycle(eq, mEngine.isProofGenerationEnabled());
		assert (res.getSize() != 2 || res.getLiteral(0).negate() != res.getLiteral(1));
		return res;
	}

	public Clause computeCycle(final CCTerm lconstant, final CCTerm rconstant) {
		final CongruencePath congPath = new CongruencePath(this);
		return congPath.computeCycle(lconstant, rconstant, mEngine.isProofGenerationEnabled());
	}

	public Clause computeAntiCycle(final CCEquality eq) {
		final CCTerm left = eq.getLhs();
		final CCTerm right = eq.getRhs();
		final CCEquality diseq = eq.mDiseqReason;
		assert left.mRepStar != right.mRepStar;
		assert diseq.getLhs().mRepStar == left.mRepStar
			|| diseq.getLhs().mRepStar == right.mRepStar;
		assert diseq.getRhs().mRepStar == left.mRepStar
			|| diseq.getRhs().mRepStar == right.mRepStar;

		left.invertEqualEdges(this);
		left.mEqualEdge = right;
		left.mOldRep = left.mRepStar;
		assert left.mOldRep.mReasonLiteral == null;
		left.mOldRep.mReasonLiteral = eq;
		final Clause c = computeCycle(diseq);
		assert left.mEqualEdge == right && left.mOldRep == left.mRepStar;
		left.mOldRep.mReasonLiteral = null;
		left.mOldRep = null;
		left.mEqualEdge = null;
		return c;
	}

	/**
	 * Compute the earliest decide level at which the path between lhs and rhs exists. There must be a path, i.e.
	 * {@code lhs.getRepresentative() == rhs.getRepresentative()}.
	 * 
	 * @param lhs
	 *            the start of the path
	 * @param rhs
	 *            the end of the path
	 * @return the earliest decide level.
	 */
	public int getDecideLevelForPath(CCTerm lhs, CCTerm rhs) {
		CongruencePath congPath = new CongruencePath(this);
		return congPath.computeDecideLevel(lhs, rhs);
	}

	public void addPending(final Literal eq) {
		assert checkPending(eq);
		mPendingLits.add(eq);
	}

	private boolean checkPending(final Literal literal) {
		if (literal.negate() instanceof CCEquality) {
			final CCEquality eq = (CCEquality) literal.negate();
			final CCTerm left = eq.getLhs();
			final CCTerm right = eq.getRhs();
			final CCEquality diseq = eq.mDiseqReason;
			assert left.mRepStar != right.mRepStar;
			assert diseq.getLhs().mRepStar == left.mRepStar
				|| diseq.getLhs().mRepStar == right.mRepStar;
			assert diseq.getRhs().mRepStar == left.mRepStar
				|| diseq.getRhs().mRepStar == right.mRepStar;
			return true;
		}
		if (literal instanceof CCEquality) {
			final CCEquality eq = (CCEquality) literal;
			return (eq.getLhs().mRepStar == eq.getRhs().mRepStar);
		}
		if (literal.getAtom() instanceof LAEquality) {
			final LAEquality laeq = (LAEquality) literal.getAtom();
			for (final CCEquality eq : laeq.getDependentEqualities()) {
				if (eq.getDecideStatus() != null
						&& eq.getDecideStatus().getSign() == literal.getSign()) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public Clause checkpoint() {
		return buildCongruence(true);
	}

	public Term convertTermToSMT(final CCTerm t) {
		return t.toSMTTerm(mEngine.getSMTTheory());
	}

	public Term convertEqualityToSMT(final CCTerm t1, final CCTerm t2) {
		return mEngine.getSMTTheory().equals(convertTermToSMT(t1),
				convertTermToSMT(t2));
	}

	public static CCEquality createEquality(final CCTerm t1, final CCTerm t2) {
		final EqualityProxy ep = t1.getFlatTerm().createEquality(t2.getFlatTerm());
		if (ep == EqualityProxy.getFalseProxy()) {
			return null;
		}
		final Literal res = ep.getLiteral(null);
		if (res instanceof CCEquality) {
			final CCEquality eq = (CCEquality) res;
			if ((eq.getLhs() == t1 && eq.getRhs() == t2) || (eq.getLhs() == t2 && eq.getRhs() == t1)) {
				return eq;
			}
		}
		return ep.createCCEquality(t1.getFlatTerm(), t2.getFlatTerm());
	}

	@Override
	public void dumpModel(final LogProxy logger) {
		// assert(checkCongruence());
		logger.info("Equivalence Classes:");
		for (final CCTerm t : mAllTerms) {
			if (t == t.mRepStar) {
				final StringBuilder sb = new StringBuilder();
				String comma = "";
				for (final CCTerm t2 : t.mMembers) {
					sb.append(comma).append(t2);
					comma = "=";
				}
				logger.info(sb.toString());
			}
		}
	}

	@SuppressWarnings("unused")
	private boolean checkCongruence() {
		boolean skip;
		for (final CCTerm t1 : mAllTerms) {
			skip = true;
			for (final CCTerm t2 : mAllTerms) {
				if (skip) {
					if (t1 == t2) {
						skip = false;
					}
					continue;
				}
				if (t1 instanceof CCAppTerm && t2 instanceof CCAppTerm) {
					final CCAppTerm a1 = (CCAppTerm) t1;
					final CCAppTerm a2 = (CCAppTerm) t2;
					if (a1.mFunc.mRepStar == a2.mFunc.mRepStar
							&& a1.mArg.mRepStar == a2.mArg.mRepStar
							&& a1.mRepStar != a2.mRepStar) {
						System.err.println("Should be congruent: " + t1 + " and " + t2);
						return false;
					}
				}
			}
		}
		return true;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		logger.info("CCTimes: iE " + mInvertEdgeTime + " eq "
				+ mEqTime + " cc " + mCcTime + " setRep "
				+ mSetRepTime);
		logger.info("Merges: " + mMergeCount + ", cc:" + mCcCount);
	}

	@Override
	public Literal getSuggestion() {
		// CClosure does not need to suggest anything so far!
		return null;
	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public Clause backtrackComplete() {
		mPendingLits.clear();
		return buildCongruence(true);
	}

	@Override
	public void restart(final int iteration) {
		// Nothing to do
	}

	@Override
	public Clause startCheck() {
		return null;
	} // NOCHECKSTYLE

	@Override
	public void endCheck() {
		// Nothing to do
	}

	void addPendingCongruence(final CCAppTerm first, final CCAppTerm second) {
		assert (first.mLeftParInfo.inList() && second.mLeftParInfo.inList());
		assert (first.mRightParInfo.inList() && second.mRightParInfo.inList());
		mPendingCongruences.add(new SymmetricPair<>(first, second));
	}

	void prependPendingCongruence(final CCAppTerm first, final CCAppTerm second) {
		assert (first.mLeftParInfo.inList() && second.mLeftParInfo.inList());
		assert (first.mRightParInfo.inList() && second.mRightParInfo.inList());
		mPendingCongruences.addFirst(new SymmetricPair<>(first, second));
	}

	/**
	 * Add all pending congruences to the CC graph.  We do not merge congruences
	 * immediately but wait for checkpoint.  Then this method is called to merge
	 * congruent function applications.
	 * @param checked if true, congruences are only applied if they still hold.
	 * @return A conflict clause if a conflict was found, null otherwise.
	 */
	private Clause buildCongruence(final boolean checked) {
		SymmetricPair<CCAppTerm> cong;
		while ((cong = mPendingCongruences.poll()) != null) {
			mEngine.getLogger().debug(new DebugMessage("PC {0}", cong));
			Clause res = null;
			final CCAppTerm lhs = cong.getFirst();
			final CCAppTerm rhs = cong.getSecond();
			// TODO Uncomment checked here
			if (/* !checked || */
					(lhs.mArg.mRepStar == rhs.mArg.mRepStar
						&& lhs.mFunc.mRepStar == rhs.mFunc.mRepStar)) {
				res = lhs.merge(this, rhs, null);
			} else {
				// assert checked : "Unchecked buildCongruence with non-holding congruence!";
				// FIXME: backtracking should filter pending congruences
			}
			if (res != null) {
				mEngine.getLogger().debug("buildCongruence: conflict %s", res);
				return res;
			}
		}
		return null;
	}

	private void backtrackStack(final int todepth) {
		while (mMerges.size() > todepth) {
			final CCTerm top = mMerges.pop();
			top.mRepStar.invertEqualEdges(this);
			final boolean isCongruence = top.mOldRep.mReasonLiteral == null;
			final CCTerm lhs = top;
			final CCTerm rhs = top.mEqualEdge;
			top.undoMerge(this, top.mEqualEdge);
			if (isCongruence) {
				assert (rhs instanceof CCAppTerm);
				prependPendingCongruence((CCAppTerm) lhs, (CCAppTerm) rhs);
			}
		}
	}

	public int getStackDepth() {
		return mMerges.size();
	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
		if (atom instanceof CCEquality) {
			final CCEquality cceq = (CCEquality) atom;
			removeCCEquality(cceq.getLhs(), cceq.getRhs(), cceq);
		}
	}

	private void removeCCEquality(CCTerm t1, CCTerm t2, final CCEquality eq) {
		// TODO Need test for this!!!
		if (t1.mMergeTime > t2.mMergeTime) {
			final CCTerm tmp = t1;
			t1 = t2;
			t2 = tmp;
		}

		if (t1.mRep == t1) {
			assert t2.mRep == t2;
			final CCTermPairHash.Info info = mPairHash.getInfo(t1, t2);
			if (info == null) {
				// We never created a pair hash for this...
				return;
			}
			info.mEqlits.prepareRemove(eq.getEntry());
			eq.getEntry().removeFromList();
			if (info.isEmpty()) {
				mPairHash.removePairInfo(info);
			}
		} else {
			final boolean isLast = t1.mRep == t2;
			boolean found = false;
			for (final CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				if (pentry.mOther == t2) {
					info.mEqlits.prepareRemove(eq.getEntry());
					found = true;
					break;
				}
			}
			assert found;
			if (isLast) {
				eq.getEntry().removeFromList();
			} else {
				removeCCEquality(t1.mRep, t2, eq);
			}
		}
		if (eq.getLASharedData() != null) {
			eq.getLASharedData().removeDependentAtom(eq);
		}
	}

	private void removeTerm(final CCTerm t) {
		assert t.mRepStar == t;
		assert mPendingCongruences.isEmpty();
		for (final Entry e : t.mPairInfos) {
			mPairHash.removePairInfo(e.getInfo());
		}
		if (t.mSharedTerm != null) {
			t.mSharedTerm = null;
		}
		if (t instanceof CCAppTerm) {
			final CCAppTerm at = (CCAppTerm) t;
			at.unlinkParentInfos();
		}
	}

	@Override
	public void pop(final Object object, final int targetlevel) {
		final StackData sd = (StackData) object;
		for (int i = mAllTerms.size() - 1; i >= sd.mAllTermsSize; --i) {
			final CCTerm t = mAllTerms.get(i);
			removeTerm(t);
			mAllTerms.remove(i);
		}
		mNumFunctionPositions = sd.mNumFuncPositions;
		mSymbolicTerms.endScope();
	}

	@Override
	public Object push() {
		mSymbolicTerms.beginScope();
		return new StackData(this);
	}

	@Override
	public Object[] getStatistics() {
		return new Object[]{
			":CC", new Object[][]{
				{"Merges", mMergeCount},
				{"Closure", mCcCount},
				{"Times", new Object[][]{
					{"Invert", mInvertEdgeTime},
					{"Eq", mEqTime},
					{"Closure", mCcTime},
					{"SetRep", mSetRepTime}}
				}
			}};
	}

	public void fillInModel(final Model model, final Theory t, final SharedTermEvaluator ste, final ArrayTheory array) {
		CCTerm trueNode = null, falseNode = null;
		if (!mAllTerms.isEmpty()) {
			final CCTerm t0 = mAllTerms.get(0);
			final SharedTerm shared0 = t0.getFlatTerm();
			if (shared0.getTerm() == t.mTrue) {
				trueNode = t0;
				falseNode = mAllTerms.get(1);
			} else if (shared0.getTerm() == t.mFalse) {
				falseNode = t0;
				trueNode = mAllTerms.get(1);
			}
		}
		trueNode.mModelVal = model.getBoolSortInterpretation().getTrueIdx();
		falseNode.mModelVal = model.getBoolSortInterpretation().getFalseIdx();
		new ModelBuilder(this, mAllTerms, model, t, ste, array, trueNode, falseNode);
	}

	void addInvertEdgeTime(final long time) {
		mInvertEdgeTime += time;
	}

	void addEqTime(final long time) {
		mEqTime += time;
	}

	void addCcTime(final long time) {
		mCcTime += time;
	}

	void addSetRepTime(final long time) {
		mSetRepTime += time;
	}

	void incCcCount() {
		++mCcCount;
	}

	void incMergeCount() {
		++mMergeCount;
	}

	void initArrays() {
		assert mNumFunctionPositions == 0 : "Solver already in use before initArrays";
		final CCBaseTerm store = new CCBaseTerm(
				true, mNumFunctionPositions, "store", null);
		mStoreNum = mNumFunctionPositions;
		mNumFunctionPositions += 3;
		mSymbolicTerms.put("store", store);
		final CCBaseTerm select = new CCBaseTerm(
				true, mNumFunctionPositions, "select", null);
		mSelectNum = mNumFunctionPositions;
		mNumFunctionPositions += 2;
		mSymbolicTerms.put("select", select);
		final CCBaseTerm diff = new CCBaseTerm(
				true, mNumFunctionPositions, "@diff", null);
		mDiffNum = mNumFunctionPositions;
		mNumFunctionPositions += 2;
		mSymbolicTerms.put("@diff", diff);
	}

	boolean isArrayTheory() {
		return mStoreNum != mSelectNum;
	}

	int getStoreNum() {
		return mStoreNum;
	}

	int getSelectNum() {
		return mSelectNum;
	}

	int getDiffNum() {
		return mDiffNum;
	}

}
