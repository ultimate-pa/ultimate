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
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.EQAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayQueue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * This class implements the theory of equality, a.k.a. congruence closure.
 *
 * This theory understands equality literals in particular CCEquality and can propagate literals that follow by
 * transitivity and/or congruence. It can also find all conflicts on these equalities. Internally it uses an equality
 * graph to represent the known equalities between terms.
 *
 * This theory can be combined with other theories using Nelson-Oppen theory combination. For every subterm in the
 * equality graph that is shared with the other theories (currently only linear arithmetic), it will propagate
 * equalities between these shared subterms when they become equal. For these shared subterms, it also creates and
 * propagates an LAEquality when the corresponding CCEquality is created/set.
 *
 * The equality graph is implemented by a union-merge data structure. The nodes in the equality graph (terms) are
 * implemented by the class CCTerm. See the description of this class for details on the implementation.
 *
 * @author Jochen Hoenicke, Jürgen Christ
 */
public class CClosure implements ITheory {
	/**
	 * The clausifier that uses this theory.
	 */
	final Clausifier mClausifier;
	/**
	 * For every term that is not a real function application of uninterpreted functions, this maps it to the
	 * corresponding cc-term, if that was created.
	 *
	 * TODO: Do we still need this? The clausifier has also a similar map.
	 */
	final Map<Term, CCTerm> mAnonTerms = new HashMap<>();
	/**
	 * The list of all cc-terms that are full function applications and thus correspond to a term.
	 *
	 * TODO: This is somewhat redundant, as the clausifier term data has also all terms.
	 */
	final ScopedArrayList<CCTerm> mAllTerms = new ScopedArrayList<>();
	/**
	 * For each pair of congruence classes this maps to the corresponding pair info. The pair info contains the list of
	 * equalities between cc-terms of the congruence classes, the first set diseq that proves that these congruence
	 * classes were disjoint, and the compare trigger for these two classes.
	 *
	 * This also contains info for non-representatives of congruence classes, namely the state, when this was last time
	 * a representative. This info is used to restore pair hash information on unmerge.
	 *
	 * @see CCTermPairHash, CCTermPairHash.Info
	 */
	final CCTermPairHash mPairHash = new CCTermPairHash();

	/**
	 * These are the list of literals that we can propagate. Each literal must be a consequence of the current
	 * congruence closure graph.
	 */
	final ArrayQueue<Literal> mPendingLits = new ArrayQueue<>();
	/**
	 * The list of CCEquality literals that were created when they were already true and thus may have been added to the
	 * wrong decision level. We need to recheck them after any backtrack, if they still can be propagated.
	 */
	ArrayQueue<Literal> mRecheckOnBacktrackLits = new ArrayQueue<>();
	/**
	 * The list of congruent terms that were already congruent when one of the terms was created and thus may be merged
	 * too late on the wrong decision level. We need to recheck after any backtrack, if they are still congruent.
	 */
	ArrayQueue<SymmetricPair<CCAppTerm>> mRecheckOnBacktrackCongs = new ArrayQueue<>();

	/**
	 * A mapping from function symbol or string (the latter only for {@code select/@diff/store}) to the corresponding
	 * CCBaseTerm that represents this function symbol.
	 *
	 * TODO: does this belong to clausifier?
	 *
	 * TODO: do we need the extra handling of {@code select/store/@diff}?
	 */
	final ScopedHashMap<Object, CCBaseTerm> mSymbolicTerms = new ScopedHashMap<>();

	/**
	 * This stores mNumFunctionPositions for every stack level.
	 *
	 * @see #mNumFunctionPositions
	 */
	final ArrayList<Integer> mNumFunctionPositionsStack = new ArrayList<>();
	/**
	 * The number of function argument positions. This is used to give each argument position in each function symbol a
	 * unique number. Two terms can only cause a congruence if they occur at the same index in the same function symbol.
	 * Thus we only need to match parent information for each such index with each other on merge.
	 *
	 * This number is used to generate a unique index for every function symbol argument position. When a new function
	 * symbol is added as a CCBaseTerm this number is used to give the arguments a unique index and this number is
	 * increased by the number of arguments of this function symbol.
	 */
	int mNumFunctionPositions;

	/**
	 * A stack containing the merges and seps that were performed on the union-find
	 * data structure. This contains the CCTerms that were the previous
	 * representative before the merge of the smaller group. Its {@code mRep} field
	 * points to the representative of the other class and should be equal to
	 * {@code mRepStar}.
	 */
	final ArrayDeque<UndoInfo> mUndoStack = new ArrayDeque<>();
	/**
	 * A list giving for each decide level the number of merges that happened before
	 * the corresponding decision.
	 */
	final ArrayDeque<Integer> mDecideLevelToUndoStackSize = new ArrayDeque<>();
	/**
	 * A list of congruences that were detected but not yet merged. These must be
	 * merged in checkpoint.
	 */
	final ArrayDeque<SymmetricPair<CCAppTerm>> mPendingCongruences = new ArrayDeque<>();

	private long mInvertEdgeTime, mEqTime, mCcTime, mSetRepTime;
	private long mCcCount, mMergeCount;

	public CClosure(final Clausifier clausifier) {
		mClausifier = clausifier;
	}

	public DPLLEngine getEngine() {
		return mClausifier.getEngine();
	}

	public LogProxy getLogger() {
		return mClausifier.getLogger();
	}

	public boolean isProofGenerationEnabled() {
		return getEngine().isProofGenerationEnabled();
	}

	public CCTerm createAnonTerm(final Term term) {
		final CCTerm ccTerm = new CCBaseTerm(false, mNumFunctionPositions, term);
		mAllTerms.add(ccTerm);
		mAnonTerms.put(term, ccTerm);
		return ccTerm;
	}

	/**
	 * Get the merge height where t1 and t2 were merged into the same congruence class.
	 * @param t1 the first term.
	 * @param t2 the second term.
	 * @return the mMergeDepth when t1 and t2 were merged.
	 */
	private int getMergeStackDepth(CCTerm t1, CCTerm t2) {
		assert t1.getRepresentative() == t2.getRepresentative() : "terms were never merged";
		if (t1 == t2) {
			return -1;
		}
		/* first compute the number of rep edges to the common representative for both terms */
		int depth1 = 0;
		int depth2 = 0;
		for (CCTerm t = t1; t != t.mRep; t = t.mRep) {
			depth1++;
		}
		for (CCTerm t = t2; t != t.mRep; t = t.mRep) {
			depth2++;
		}
		/*
		 * Move to the common ancestor. If the common ancestor is one of the terms, the previous edge gives us the merge
		 * time.
		 */
		while (depth1 > depth2) {
			if (t1.mRep == t2) {
				return t1.mMergeTime;
			}
			t1 = t1.mRep;
			depth1--;
		}
		assert t1 != t2;
		while (depth2 > depth1) {
			if (t2.mRep == t1) {
				return t2.mMergeTime;
			}
			t2 = t2.mRep;
			depth2--;
		}
		assert t1 != t2;
		assert depth2 == depth1;
		/*
		 * If the common ancestor is not one of the two terms, we find it here. One of the previous edges merged t1 and
		 * t2, namely the one that happened later.
		 */
		while (true) {
			assert t1 != t2;
			assert t1 != t1.mRep;
			assert t2 != t2.mRep;
			if (t1.mRep == t2.mRep) {
				return Math.max(t1.mMergeTime, t2.mMergeTime);
			}
			t1 = t1.mRep;
			t2 = t2.mRep;
		}
	}

	/**
	 * Searches for the congruent term of {@code CCAppTerm(func,arg)} that would have been merged on the lowest decision
	 * level.
	 *
	 * @param func
	 *            The CCTerm representing the function.
	 * @param arg
	 *            The CCTerm representing the argument.
	 * @return The congruent CCAppTerm or null if there is no congruent application.
	 */
	private CCAppTerm findCongruentAppTerm(final CCTerm func, final CCTerm arg) {
		final CCParentInfo argInfo = arg.getRepresentative().mCCPars.getInfo(func.mParentPosition);
		int congruenceLevel = Integer.MAX_VALUE;
		CCAppTerm congruentTerm = null;
		// Look for all congruent terms for the argument.
		for (final Parent p : argInfo.mCCParents) {
			final CCAppTerm papp = p.getData();
			final CCTerm pfunc = papp.getFunc();
			final CCTerm parg = papp.getArg();
			assert parg.getRepresentative() == arg.getRepresentative();
			if (pfunc.getRepresentative() != func.getRepresentative()) {
				// this term is not congruent
				continue;
			}
			if (pfunc == func && parg == arg) {
				// this is the app term for which we search a congruent term; skip it
				continue;
			}
			// compute the level where the congruence occurred
			final int level = Math.max(getMergeStackDepth(pfunc, func), getMergeStackDepth(parg, arg));
			// store the congruence with the smallest level
			if (level < congruenceLevel) {
				congruenceLevel = level;
				congruentTerm = papp;
			}
		}
		return congruentTerm;
	}

	public CCAppTerm createAppTerm(final boolean isFunc, final CCTerm func, final CCTerm arg,
			final SourceAnnotation source) {
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
		final CCAppTerm term = new CCAppTerm(isFunc, isFunc ? func.mParentPosition + 1 : 0, func, arg, this,
				source.isFromQuantTheory());
		if (!isFunc) {
			if (term.getAge() > 0) {
				getLogger().debug("Create new AppTerm %s of age %d", term, term.getAge());
			}
		}
		mAllTerms.add(term);
		term.addParentInfo(this);
		final CCAppTerm congruentTerm = findCongruentAppTerm(func, arg);
		getLogger().debug("createAppTerm %s congruent: %s", term, congruentTerm);
		if (congruentTerm != null) {
			// Here, we do not have the resulting term in the equivalence class
			// Mark pending congruence
			mRecheckOnBacktrackCongs.add(new SymmetricPair<>(term, congruentTerm));
			addPendingCongruence(term, congruentTerm);
		}

		if (!isFunc) {
			/* if this created a complete application term, activate corresponding triggers */
			CCTerm partialApp = term;
			while (partialApp instanceof CCAppTerm) {
				final CCAppTerm app = (CCAppTerm) partialApp;
				final CCTerm appArg = app.getArg();
				/* E-Matching: activate reverse trigger */
				final int parentpos = app.getFunc().mParentPosition;
				final CCParentInfo argInfo = appArg.getRepresentative().mCCPars.getInfo(parentpos);
				if (argInfo != null) {
					for (final ReverseTrigger trigger : argInfo.mReverseTriggers) {
						trigger.activate(term, true);
					}
				}
				partialApp = app.getFunc();
			}
			/* E-Matching: activate find trigger */
			{
				final CCParentInfo funcInfo = partialApp.mCCPars.getInfo(0);
				if (funcInfo != null) {
					for (final ReverseTrigger trigger : funcInfo.mReverseTriggers) {
						trigger.activate(term, true);
					}
				}
			}
		}
		return term;
	}

	/**
	 * Function to retrieve the CCTerm representing a function symbol.
	 *
	 * @param sym
	 *            Function symbol.
	 * @return CCTerm representing this function symbol in the egraph.
	 */
	public CCTerm getFuncTerm(final FunctionSymbol sym) {
		CCBaseTerm term = mSymbolicTerms.get(sym);
		if (term == null) {
			term = new CCBaseTerm(sym.getParameterSorts().length > 0, mNumFunctionPositions, sym);
			mAllTerms.add(term);
			mNumFunctionPositions += sym.getParameterSorts().length;
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
	 * Get all (complete) function applications of a given function symbol with a given argument at a given position.
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
		if (info != null) {
			for (final Parent parent : info.mCCParents) {
				if (!parent.isMarked()) {
					funcApps.add(parent.getData());
				}
			}
			for (int i = argPos + 1; i < sym.getParameterSorts().length; i++) {
				funcApps = getApplications(funcApps);
			}
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
		if (!mAllTerms.contains(t1) || !mAllTerms.contains(t2)) {
			return; // FIXME This is a workaround for the problem that pop() first removes terms, then triggers, as it
			// is executed for CClosure first. Then this method can be called for a trigger where the
			// corresponding terms have already been removed.
		}
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
				final CCTermPairHash.Info info = mPairHash.getInfo(t1, t2);
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
		if (!mAllTerms.contains(termWithTrigger)) {
			return; // FIXME This is a workaround for the problem that pop() first removes terms, then triggers, as it
			// is executed for CClosure first. Then this method can be called for a trigger where the
			// corresponding term has already been removed.
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
		return first.getRepresentative() == second.getRepresentative();
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
		return diseqInfo != null && diseqInfo.mDiseq != null;
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

	public CCEquality createCCEquality(final int stackLevel, CCTerm t1, CCTerm t2) {
		assert (t1 != t2);
		CCEquality eq = null;
		assert t1.invariant();
		assert t2.invariant();

		// to make cc equalities different from la equalities, ensure that t2 is not a
		// constant.
		if (t2.getFlatTerm().getSort().isNumericSort() && (t2.getFlatTerm() instanceof ConstantTerm)) {
			final CCTerm tmp = t2;
			t2 = t1;
			t1 = tmp;
		}
		eq = new CCEquality(stackLevel, t1, t2);
		insertEqualityEntry(t1, t2, eq.getEntry());
		getEngine().addAtom(eq);

		assert t1.invariant();
		assert t2.invariant();
		assert t1.pairHashValid(this);
		assert t2.pairHashValid(this);

		if (t1.mRepStar == t2.mRepStar) {
			if (getLogger().isDebugEnabled()) {
				getLogger().debug("CC-Prop: " + eq + " repStar: " + t1.mRepStar);
			}
			mPendingLits.add(eq);
			mRecheckOnBacktrackLits.add(eq);
		} else {
			final CCEquality diseq = mPairHash.getInfo(t1.mRepStar, t2.mRepStar).mDiseq;
			if (diseq != null) {
				if (getLogger().isDebugEnabled()) {
					getLogger().debug("CC-Prop: " + eq.negate() + " diseq: " + diseq);
				}
				eq.mDiseqReason = diseq;
				mPendingLits.add(eq.negate());
				mRecheckOnBacktrackLits.add(eq.negate());
			}
		}
		return eq;
	}

	public void addTerm(final CCTerm ccterm, final Term term) {
		ccterm.mFlatTerm = term;
	}

	public void addSharedTerm(final CCTerm ccterm) {
		ccterm.share(this);
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
				if (eq.getStackPosition() >= 0 && eq.getStackPosition() < laeq.getStackPosition()
						&& eq.getDecideStatus().getSign() == lit.getSign()) {
					return new Clause(new Literal[] { eq.getDecideStatus().negate(), lit },
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

	/**
	 * Record a merge step on the undo stack. This should only be called by
	 * CCTerm.mergeInternal.
	 *
	 * @param oldRep the old representative (of the smaller class) that was merged.
	 */
	void recordMerge(final CCTerm oldRep) {
		mUndoStack.push(new MergeUndoInfo(oldRep));
	}

	/**
	 * Get the merge depth, i.e., the number of merges that already happened. We use
	 * the undo stack, so we also count separations, but that shouldn't matter.
	 *
	 * @return the merge depth (non-negative integer).
	 */
	int getMergeDepth() {
		return mUndoStack.size();
	}

	@Override
	public Clause setLiteral(final Literal literal) {
		if (!(literal.getAtom() instanceof CCEquality)) {
			return null;
		}
		final CCEquality eq = (CCEquality) literal.getAtom();
		if (literal == eq) {
			if (eq.getLhs().mRepStar != eq.getRhs().mRepStar) {
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
		}
		final LAEquality laeq = eq.getLASharedData();
		if (laeq != null) {
			assert ((List<CCEquality>) laeq.getDependentEqualities()).contains(eq);
			if (laeq.getDecideStatus() != null && laeq.getDecideStatus().getSign() != literal.getSign()) {
				return new Clause(new Literal[] { laeq.getDecideStatus().negate(), literal.negate() },
						new LeafNode(LeafNode.EQ, EQAnnotation.EQ));
			}
			mPendingLits.add(literal == eq ? laeq : laeq.negate());
		}
		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
	}

	void removePairHash(final CCTermPairHash.Info info) {
		mPairHash.remove(info);
	}

	private void separate(final CCTerm lhs, final CCTerm rhs, final CCEquality diseq) {
		final CCEquality reason = diseq.mDiseqReason;
		/*
		 * Check if this is a propagated equality. We need to check if the diseq reason
		 * is asserted and that it is still the same equivalence class. This is because
		 * the diseq reason is not reset on backtrack.
		 */
		if (reason != null && reason.getDecideStatus() == reason.negate()) {
			if (reason.getLhs().getRepresentative() == lhs && reason.getRhs().getRepresentative() == rhs) {
				return;
			}
			if (reason.getLhs().getRepresentative() == rhs && reason.getRhs().getRepresentative() == lhs) {
				return;
			}
		}
		final CCTermPairHash.Info info = mPairHash.getInfo(lhs, rhs);
		assert info.mDiseq == null;

		mUndoStack.push(new SepUndoInfo(diseq));
		info.mDiseq = diseq;
		/* Propagate inequalities */
		for (final CCEquality.Entry eqentry : info.mEqlits) {
			final CCEquality eq = eqentry.getCCEquality();
			assert eq.getDecideStatus() == null || eq == diseq;
			if (eq.getDecideStatus() == null) {
				eq.mDiseqReason = diseq;
				addPending(eq.negate());
			}
		}
	}

	private void undoSep(final CCEquality atom) {
		final CCTermPairHash.Info destInfo = mPairHash.getInfo(atom.getLhs().mRepStar, atom.getRhs().mRepStar);
		assert destInfo != null && destInfo.mDiseq == atom;
		destInfo.mDiseq = null;
	}

	public Clause computeCycle(final CCEquality eq) {
		final CongruencePath congPath = new CongruencePath(this);
		final Clause res = congPath.computeCycle(eq, isProofGenerationEnabled());
		assert (res.getSize() != 2 || res.getLiteral(0).negate() != res.getLiteral(1));
		return res;
	}

	public Clause computeCycle(final CCTerm lconstant, final CCTerm rconstant) {
		final CongruencePath congPath = new CongruencePath(this);
		return congPath.computeCycle(lconstant, rconstant, isProofGenerationEnabled());
	}

	public Clause computeAntiCycle(final CCEquality eq) {
		final CCTerm left = eq.getLhs();
		final CCTerm right = eq.getRhs();
		final CCEquality diseq = eq.mDiseqReason;
		assert left.mRepStar != right.mRepStar;
		assert diseq.getLhs().mRepStar == left.mRepStar || diseq.getLhs().mRepStar == right.mRepStar;
		assert diseq.getRhs().mRepStar == left.mRepStar || diseq.getRhs().mRepStar == right.mRepStar;

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
	public int getDecideLevelForPath(final CCTerm lhs, final CCTerm rhs) {
		final CongruencePath congPath = new CongruencePath(this);
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
			assert diseq.getLhs().mRepStar == left.mRepStar || diseq.getLhs().mRepStar == right.mRepStar;
			assert diseq.getRhs().mRepStar == left.mRepStar || diseq.getRhs().mRepStar == right.mRepStar;
			return true;
		}
		if (literal instanceof CCEquality) {
			final CCEquality eq = (CCEquality) literal;
			return (eq.getLhs().mRepStar == eq.getRhs().mRepStar);
		}
		if (literal.getAtom() instanceof LAEquality) {
			final LAEquality laeq = (LAEquality) literal.getAtom();
			for (final CCEquality eq : laeq.getDependentEqualities()) {
				if (eq.getDecideStatus() != null && eq.getDecideStatus().getSign() == literal.getSign()) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public Clause checkpoint() {
		return buildCongruence();
	}

	public CCEquality createEquality(final CCTerm t1, final CCTerm t2, final boolean createLAEquality) {
		assert t1 != t2;
		final EqualityProxy ep = mClausifier.createEqualityProxy(t1.getFlatTerm(), t2.getFlatTerm(), null);
		if (ep == EqualityProxy.getFalseProxy()) {
			return null;
		}
		if (!createLAEquality) {
			final Literal res = ep.getLiteral(null);
			if (res instanceof CCEquality) {
				final CCEquality eq = (CCEquality) res;
				if ((eq.getLhs() == t1 && eq.getRhs() == t2) || (eq.getLhs() == t2 && eq.getRhs() == t1)) {
					return eq;
				}
			}
		}
		return ep.createCCEquality(t1.getFlatTerm(), t2.getFlatTerm());
	}

	@Override
	public void dumpModel(final LogProxy logger) {
		// assert(checkCongruence());
		logger.info("Equivalence Classes:");
		for (final CCTerm t : mAllTerms) {
			if (t == t.mRepStar && !t.isFunc()) {
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

	private boolean checkCongruence() {
		boolean skip;
		for (final CCTerm t1 : mAllTerms) {
			assert t1.invariant();
			if (!(t1 instanceof CCAppTerm)) {
				continue;
			}
			final CCAppTerm a1 = (CCAppTerm) t1;
			skip = true;
			for (final CCTerm t2 : mAllTerms) {
				// don't check symmetric cases: skip all terms in the inner loop up to and including the term t1.
				// Thus we check exactly the pairs (t1,t2) where t1 occurs (strictly) before t2 in mAllTerms.
				if (skip) {
					if (t1 == t2) {
						skip = false;
					}
					continue;
				}
				if (t1.getRepresentative() != t2.getRepresentative() && t2 instanceof CCAppTerm) {
					final CCAppTerm a2 = (CCAppTerm) t2;
					if (a1.getFunc().getRepresentative() == a2.getFunc().getRepresentative()
							&& a1.getArg().getRepresentative() == a2.getArg().getRepresentative()) {
						getLogger().fatal("Should be congruent: " + t1 + " and " + t2);
						return false;
					}
				}
			}
		}
		return true;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		logger.info("CCTimes: iE " + mInvertEdgeTime + " eq " + mEqTime + " cc " + mCcTime + " setRep " + mSetRepTime);
		logger.info("Merges: " + mMergeCount + ", cc:" + mCcCount);
	}

	@Override
	public Literal getSuggestion() {
		// CClosure does not need to suggest anything so far!
		return null;
	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		final int mergeStackLevel = mDecideLevelToUndoStackSize.pop();
		assert mDecideLevelToUndoStackSize.size() == currentDecideLevel;
		backtrackStack(mergeStackLevel);
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		mDecideLevelToUndoStackSize.push(mUndoStack.size());
		assert mDecideLevelToUndoStackSize.size() == currentDecideLevel;
	}

	@Override
	public void backtrackStart() {
		mPendingLits.clear();
		mPendingCongruences.clear();
	}

	@Override
	public Clause backtrackComplete() {
		/*
		 * If a literal was propagated when it was created it may not be on the right decision level. After backtracking
		 * we may need to propagate these literals again, if they are still implied by the CC graph. Here we go through
		 * the list of all such literals and check if we ned to propagate them again.
		 */
		final ArrayQueue<Literal> newRecheckOnBacktrackLits = new ArrayQueue<>();
		for (final Literal l : mRecheckOnBacktrackLits) {
			final CCEquality eq = (CCEquality) l.getAtom();
			if (eq.getDecideStatus() != null) {
				/* We did not yet backtrack the literal; keep it for later */
				newRecheckOnBacktrackLits.add(l);
				/* It may have an LAEquality that was backtracked. Then we need to propagate the LAEquality. */
				final LAEquality laeq = eq.getLASharedData();
				if (laeq != null && laeq.getDecideStatus() == null) {
					getLogger().debug("repropagating LAEQ: %s -> %s", eq, laeq);
					mPendingLits.add(l == eq ? laeq : laeq.negate());
				}
				continue;
			}
			final CCTerm lhs = eq.getLhs().getRepresentative();
			final CCTerm rhs = eq.getRhs().getRepresentative();
			/* check if literal is still implied by the graph */
			boolean repropagate = false;
			if (l.getSign() > 0) {
				repropagate = (lhs == rhs);
			} else {
				final CCEquality diseq = mPairHash.getInfo(lhs, rhs).mDiseq;
				if (diseq != null) {
					eq.mDiseqReason = diseq;
					repropagate = true;
				}
			}
			/* repropagate the literal by adding it to the pending literals. */
			if (repropagate) {
				getLogger().debug("CC-ReProp: %s", l);
				mPendingLits.add(l);
				newRecheckOnBacktrackLits.add(l);
			}
		}
		/*
		 * Recheck the propagated literals again on the next backtrack.
		 */
		mRecheckOnBacktrackLits = newRecheckOnBacktrackLits;

		/*
		 * Recheck congruences and propagate them.
		 */
		final ArrayQueue<SymmetricPair<CCAppTerm>> newRecheckOnBacktrackCongs = new ArrayQueue<>();
		for (final SymmetricPair<CCAppTerm> cong : mRecheckOnBacktrackCongs) {
			final CCAppTerm lhs = cong.getFirst();
			final CCAppTerm rhs = cong.getSecond();
			if (lhs.mArg.mRepStar == rhs.mArg.mRepStar && lhs.mFunc.mRepStar == rhs.mFunc.mRepStar) {
				getLogger().debug("Still congruent: %s and %s", lhs, rhs);
				addPendingCongruence(lhs, rhs);
				newRecheckOnBacktrackCongs.add(cong);
			} else {
				getLogger().debug("No longer congruent: %s and %s", lhs, rhs);
			}
		}
		mRecheckOnBacktrackCongs = newRecheckOnBacktrackCongs;
		return buildCongruence();
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
		getLogger().debug("addPendingCongruence: %s %s", first, second);
		mPendingCongruences.add(new SymmetricPair<>(first, second));
	}

	/**
	 * Add all pending congruences to the CC graph. We do not merge congruences immediately but wait for checkpoint.
	 * Then this method is called to merge congruent function applications.
	 *
	 * @param checked
	 *            if true, congruences are only applied if they still hold.
	 * @return A conflict clause if a conflict was found, null otherwise.
	 */
	@SuppressWarnings("unused")
	private Clause buildCongruence() {
		SymmetricPair<CCAppTerm> cong;
		while ((cong = mPendingCongruences.poll()) != null) {
			getLogger().debug("PC %s", cong);
			final CCAppTerm lhs = cong.getFirst();
			final CCAppTerm rhs = cong.getSecond();
			assert lhs.mArg.mRepStar == rhs.mArg.mRepStar
					&& lhs.mFunc.mRepStar == rhs.mFunc.mRepStar : "Unchecked buildCongruence with non-holding congruence!";
			final Clause res = lhs.merge(this, rhs, null);
			if (res != null) {
				getLogger().debug("buildCongruence: conflict %s", res);
				return res;
			}
		}
		assert !Config.EXPENSIVE_ASSERTS || checkCongruence();
		return null;
	}

	private void backtrackStack(final int todepth) {
		while (mUndoStack.size() > todepth) {
			final UndoInfo top = mUndoStack.pop();
			if (top instanceof MergeUndoInfo) {
				final CCTerm oldRep = ((MergeUndoInfo) top).getOldRep();
				oldRep.mRepStar.invertEqualEdges(this);
				oldRep.undoMerge(this, oldRep.mEqualEdge);
			} else {
				final CCEquality diseq = ((SepUndoInfo) top).getDiseq();
				undoSep(diseq);
			}
		}
	}

	public int getStackDepth() {
		return mUndoStack.size();
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
			if (info != null) {
				// Remove pair hash info
				info.mEqlits.prepareRemove(eq.getEntry());
				eq.getEntry().removeFromList();
				if (info.isEmpty()) {
					mPairHash.removePairInfo(info);
				}
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
		while (!t.mPairInfos.isEmpty()) {
			final CCTermPairHash.Info info = t.mPairInfos.iterator().next().getInfo();
			mPairHash.removePairInfo(info);
		}
		if (t instanceof CCAppTerm) {
			final CCAppTerm at = (CCAppTerm) t;
			at.unlinkParentInfos();
		}
	}

	@Override
	public void backtrackAll() {
		assert mDecideLevelToUndoStackSize.isEmpty();
		backtrackStack(0);
		mPendingLits.clear();
		mRecheckOnBacktrackCongs.clear();
		mRecheckOnBacktrackLits.clear();
		mPendingCongruences.clear();
	}

	@Override
	public void pop() {
		assert mDecideLevelToUndoStackSize.isEmpty();
		assert mUndoStack.isEmpty();
		assert mRecheckOnBacktrackCongs.isEmpty();
		assert mRecheckOnBacktrackLits.isEmpty();
		assert mPendingCongruences.isEmpty();
		mNumFunctionPositions = mNumFunctionPositionsStack.remove(mNumFunctionPositionsStack.size() - 1);
		for (final CCTerm t : mAllTerms.currentScope()) {
			removeTerm(t);
		}
		mAllTerms.endScope();
		mSymbolicTerms.endScope();
	}

	@Override
	public void push() {
		mSymbolicTerms.beginScope();
		mAllTerms.beginScope();
		mNumFunctionPositionsStack.add(mNumFunctionPositions);
	}

	@Override
	public Object[] getStatistics() {
		return new Object[] { ":CC",
				new Object[][] { { "Merges", mMergeCount }, { "Closure", mCcCount },
						{ "Times", new Object[][] { { "Invert", mInvertEdgeTime }, { "Eq", mEqTime },
								{ "Closure", mCcTime }, { "SetRep", mSetRepTime } } } } };
	}

	public void fillInModel(final Model model, final Theory t, final SharedTermEvaluator ste,
			final ArrayTheory arrayTheory, final DataTypeTheory datatypeTheory) {
		final CCTerm trueNode = mClausifier.getCCTerm(t.mTrue);
		final CCTerm falseNode = mClausifier.getCCTerm(t.mFalse);
		new ModelBuilder(this, mAllTerms, model, t, ste, arrayTheory, datatypeTheory, trueNode, falseNode);
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

	private static class UndoInfo {
	}

	private static class MergeUndoInfo extends UndoInfo {
		final CCTerm mOldRep;

		public MergeUndoInfo(final CCTerm oldRep) {
			mOldRep = oldRep;
		}

		public CCTerm getOldRep() {
			return mOldRep;
		}
	}

	private static class SepUndoInfo extends UndoInfo {
		CCEquality mDiseq;

		public SepUndoInfo(final CCEquality diseq) {
			mDiseq = diseq;
		}

		public CCEquality getDiseq() {
			return mDiseq;
		}
	}
}
