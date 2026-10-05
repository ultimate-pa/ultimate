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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.FindTriggerTrigger.AppTermEntry;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.EQAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayQueue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * This class implements the theory of equality, a.k.a. congruence closure.
 *
 * This theory understands equality literals in particular CCEquality and can
 * propagate literals that follow by transitivity and/or congruence. It can also
 * find all conflicts on these equalities. Internally it uses an equality graph
 * to represent the known equalities between terms.
 *
 * This theory can be combined with other theories using Nelson-Oppen theory
 * combination. For every subterm in the equality graph that is shared with the
 * other theories (currently only linear arithmetic), it will propagate
 * equalities between these shared subterms when they become equal. For these
 * shared subterms, it also creates and propagates an LAEquality when the
 * corresponding CCEquality is created/set.
 *
 * The equality graph is implemented by a union-merge data structure. The nodes
 * in the equality graph (terms) are implemented by the class CCTerm. See the
 * description of this class for details on the implementation.
 *
 * @author Jochen Hoenicke, Jürgen Christ
 */
public class CClosure implements ITheory {
	/**
	 * The clausifier that uses this theory.
	 */
	final Clausifier mClausifier;
	/**
	 * For every term that is not a real function application of uninterpreted
	 * functions, this maps it to the corresponding cc-term, if that was created.
	 *
	 * TODO: Do we still need this? The clausifier has also a similar map.
	 */
	final Map<Term, CCTerm> mAnonTerms = new HashMap<>();
	/**
	 * The list of all cc-terms that are full function applications and thus
	 * correspond to a term.
	 *
	 * TODO: This is somewhat redundant, as the clausifier term data has also all
	 * terms.
	 */
	final ScopedArrayList<CCTerm> mAllTerms = new ScopedArrayList<>();
	/**
	 * For each pair of congruence classes this maps to the corresponding pair info.
	 * The pair info contains the list of equalities between cc-terms of the
	 * congruence classes, the first set diseq that proves that these congruence
	 * classes were disjoint, and the compare trigger for these two classes.
	 *
	 * This also contains info for non-representatives of congruence classes, namely
	 * the state, when this was last time a representative. This info is used to
	 * restore pair hash information on unmerge.
	 *
	 * @see CCTermPairHash, CCTermPairHash.Info
	 */
	final CCTermPairHash mPairHash = new CCTermPairHash();

	/**
	 * These are the list of literals that we can propagate. Each literal must be a
	 * consequence of the current congruence closure graph.
	 */
	final ArrayQueue<Literal> mPendingLits = new ArrayQueue<>();
	/**
	 * The list of CCEquality literals that were created when they were already true
	 * and thus may have been added to the wrong decision level. We need to recheck
	 * them after any backtrack, if they still can be propagated.
	 */
	ArrayQueue<Literal> mRecheckOnBacktrackLits = new ArrayQueue<>();

	/**
	 * A mapping from function symbol or string (the latter only for
	 * {@code select/@diff/store}) to the corresponding CCBaseTerm that represents
	 * this function symbol.
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
	 * The number of function argument positions. This is used to give each argument
	 * position in each function symbol a unique number. Two terms can only cause a
	 * congruence if they occur at the same index in the same function symbol. Thus
	 * we only need to match parent information for each such index with each other
	 * on merge.
	 *
	 * This number is used to generate a unique index for every function symbol
	 * argument position. When a new function symbol is added as a CCBaseTerm this
	 * number is used to give the arguments a unique index and this number is
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

	/**
	 * Global map from signature to trigger. Used for congruence finder and reverse
	 * triggers. Signatures are rehashed at checkpoint when the todo is processed.
	 * When a representative changes, the affected signature is taken out of this
	 * map ({@link #moveToSignatureTodo}) and appended to {@link #mSignatureTodo};
	 * the next checkpoint puts the same key back ({@link #addSignatureHash}), where
	 * it now maps to a new bucket since its hashCode/equals use representatives and
	 * offsets. We do not keep the old key in the map, since that would leave the map
	 * inconsistent.
	 */
	final Map<SignatureTrigger, SignatureTrigger> mSignatureTriggers = new HashMap<>();
	/**
	 * Todo list of deferred signatures.
	 */
	final SimpleList<SignatureTrigger> mSignatureTodo = new SimpleList<SignatureTrigger>();
	/**
	 * The master reverse triggers of this engine, one per (function symbol, argument position) pair, see
	 * {@link MasterReverseTrigger#of}. This must be per engine (not a global unifier): solver instances may share the
	 * theory and thus the function symbols, but each engine needs its own find trigger registration.
	 */
	private final UnifyHash<MasterReverseTrigger> mMasterReverseTriggers = new UnifyHash<>();

	private long mInvertEdgeTime, mEqTime, mCcTime, mSetRepTime, mSigHashTime;
	private long mCcCount, mMergeCount;

	public CClosure(final Clausifier clausifier) {
		mClausifier = clausifier;
	}

	UnifyHash<MasterReverseTrigger> getMasterReverseTriggers() {
		return mMasterReverseTriggers;
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

	/**
	 * Whether offset equalities are created. When enabled, arithmetic terms are turned into offset-free CCTerms (with
	 * the constant carried as an offset) and equalities between numeric terms become offset equalities, so that a
	 * congruence class is an affine class: every member has a known constant offset to the representative. When
	 * disabled, every offset is zero and the structure degenerates to plain congruence closure.
	 *
	 * The flag itself lives in the clausifier, which builds the terms, so that the two cannot disagree.
	 */
	public boolean createOffsetEqualities() {
		return mClausifier.createOffsetEqualities();
	}

	public CCTerm createAnonTerm(final Term term) {
		final CCTerm ccTerm = new CCBaseTerm(term);
		mAllTerms.add(ccTerm);
		mAnonTerms.put(term, ccTerm);
		return ccTerm;
	}

	/**
	 * Get the merge height where t1 and t2 were merged into the same congruence
	 * class.
	 *
	 * @param t1 the first term.
	 * @param t2 the second term.
	 * @return the mMergeDepth when t1 and t2 were merged.
	 */
	private int getMergeStackDepth(CCTerm t1, CCTerm t2) {
		assert t1.getRepresentative() == t2.getRepresentative() : "terms were never merged";
		if (t1 == t2) {
			return -1;
		}
		/*
		 * first compute the number of rep edges to the common representative for both
		 * terms
		 */
		int depth1 = 0;
		int depth2 = 0;
		for (CCTerm t = t1; t != t.mRep; t = t.mRep) {
			depth1++;
		}
		for (CCTerm t = t2; t != t.mRep; t = t.mRep) {
			depth2++;
		}
		/*
		 * Move to the common ancestor. If the common ancestor is one of the terms, the
		 * previous edge gives us the merge time.
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
		 * If the common ancestor is not one of the two terms, we find it here. One of
		 * the previous edges merged t1 and t2, namely the one that happened later.
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
	 * Create a function application CCTerm. Each argument is a {@link CCParameter}, i.e. a CCTerm together with a
	 * constant offset, so the actual argument is {@code args[i].getCCTerm() + args[i].getOffset()} (the offset carries
	 * e.g. the {@code +5} in {@code f(x+5)}). Offset-free arguments are bare {@link CCTerm}s.
	 */
	public CCTerm createAppTerm(FunctionSymbol func, final CCParameter[] args, final SourceAnnotation source) {
		assert args.length > 0;
		if (args.length > 0) {
			final CCAppTerm term = new CCAppTerm(func, args, this, source.isFromQuantTheory());
			if (term.getAge() > 0) {
				getLogger().debug("Create new AppTerm %s of age %d", term, term.getAge());
			}
			final CongruenceTrigger congruenceTrigger = new CongruenceTrigger(term, func, args);
			term.mCongTrigger = congruenceTrigger;
			term.mFindTrigger = new FindTriggerTrigger(term);
			addSignature(congruenceTrigger);
			addSignature(term.mFindTrigger);
			mAllTerms.add(term);
			return term;
		} else {
			final CCBaseTerm term = new CCBaseTerm(func);
			mAllTerms.add(term);
			return term;
		}
	}

	/**
	 * Get all terms that are a (complete) function application of the given
	 * function symbol.
	 *
	 * @param sym the function symbol.
	 * @return all function applications of the given function symbol.
	 */
	public List<CCAppTerm> getAllFuncApps(final FunctionSymbol sym) {
		final SignatureTrigger sig = new SignatureTrigger(sym, new CCTerm[0]);
		final FindTriggerTrigger findTrigger = (FindTriggerTrigger) mSignatureTriggers.get(sig);
		if (findTrigger == null) {
			return Collections.emptyList();
		}
		final List<CCAppTerm> parents = new ArrayList<>();
		for (final AppTermEntry appTerm : findTrigger.getApplications()) {
			parents.add(appTerm.getAppTerm());
		}
		return parents;
	}

	/** Pseudo argument position of the array element-value group, see {@link #getNumericClashSlots}. */
	private static final int POS_ARRAY_ELEMENT = -1;

	/**
	 * Key of a numeric clash slot: a (function symbol, argument position) pair, or, for the array element-value group,
	 * the array sort together with {@link #POS_ARRAY_ELEMENT}. Both function symbols and sorts are unified by the
	 * theory, so the key compares them by identity.
	 */
	private static final class ClashKey {
		final Object mSym;
		final int mPos;

		ClashKey(final Object sym, final int pos) {
			mSym = sym;
			mPos = pos;
		}

		@Override
		public int hashCode() {
			return mSym.hashCode() * 31 + mPos;
		}

		@Override
		public boolean equals(final Object other) {
			if (!(other instanceof ClashKey)) {
				return false;
			}
			final ClashKey key = (ClashKey) other;
			return mSym == key.mSym && mPos == key.mPos;
		}
	}

	/**
	 * Enumerate the numeric clash slots for model-based theory combination, on demand. A clash slot groups the
	 * {@link CCParameter}s occupying one (function symbol, argument position) whose argument sort is numeric. Two
	 * members of the same slot with equal value but in distinct congruence classes are an equality that MBTC may
	 * propose: merging them is what makes the two applications congruent at that position. Only members whose class
	 * has a linear-arithmetic value ({@code getRepresentative().getSharedTerm() != null}) are kept &mdash; a class
	 * without a shared term is free to receive a non-clashing value at model construction, so it cannot be forced to
	 * clash.
	 * <p>
	 * MBTC runs only in {@code finalCheck}, so the slots are computed on demand here rather than maintained in a
	 * persistent, backtracked index; the signature todo queue is drained at every checkpoint, so all installed
	 * reverse triggers are in the signature map by then.
	 * <p>
	 * Three sources are enumerated: the <em>congruence</em> source (every function-application argument position), the
	 * <em>reverse-trigger</em> source &mdash; an installed reverse trigger (e.g. from e-matching) watches a (symbol,
	 * position) for applications whose argument has the watched value, so that value is a slot member, too: an MBTC
	 * merge that moves an argument onto it activates the trigger &mdash; and the <em>array element-value</em> source
	 * described below. The deferred datatype numeric-field feed is still future work.
	 * <p>
	 * The array element-value group exists because {@link ArrayTheory} reads distinct congruence classes as distinct
	 * values: its weakeq-ext fingerprints (and the weakeq propagations) tell two arrays apart by comparing the classes
	 * of their element values, so if two such classes end up with the same value in the model, an array disequality
	 * silently becomes false there. The element values it compares are the select applications of its {@code mSelects}
	 * maps and the values of {@code const} arrays, so both are collected into one group per array sort &mdash; one
	 * group, since a const value must also be comparable to a select value (read-const-weakeq), which per-(symbol,
	 * position) slots can never do. Store values need no entry of their own: {@code addStoreAxiom} always asserts
	 * {@code (= (select (store a i v) i) v)}, so the class of {@code v} contains a select application.
	 *
	 * @return the slots as lists of members; each list holds the numeric, LA-valued members at one (symbol, position)
	 *         or the numeric element values of one array sort.
	 */
	public Collection<List<CCParameter>> getNumericClashSlots() {
		final Map<ClashKey, List<CCParameter>> slots = new LinkedHashMap<>();
		for (final CCTerm term : mAllTerms) {
			if (!(term instanceof CCAppTerm)) {
				continue;
			}
			final CCAppTerm app = (CCAppTerm) term;
			final FunctionSymbol sym = app.getFunctionSymbol();
			for (int pos = 0; pos < app.getArgCount(); pos++) {
				addClashMember(slots, new ClashKey(sym, pos), app.getArgParam(pos));
			}
			addArrayElementValue(slots, app);
		}
		for (final SignatureTrigger sigTrigger : mSignatureTriggers.values()) {
			if (!(sigTrigger instanceof ReverseTriggerTrigger)) {
				continue;
			}
			for (final ReverseTrigger trigger : ((ReverseTriggerTrigger) sigTrigger).getTriggers()) {
				final CCParameter arg = trigger.getArgument();
				if (arg != null && trigger.getArgPosition() >= 0) {
					addClashMember(slots, new ClashKey(trigger.getFunctionSymbol(), trigger.getArgPosition()), arg);
				}
			}
		}
		return slots.values();
	}

	/**
	 * Feed the array element-value group of one application: a select application contributes its own value, a
	 * {@code const} application the value it is filled with. See {@link #getNumericClashSlots}.
	 */
	private static void addArrayElementValue(final Map<ClashKey, List<CCParameter>> slots, final CCAppTerm app) {
		final String name = app.getFunctionSymbol().getName();
		final Sort arraySort;
		final CCParameter value;
		if (name.equals(SMTLIBConstants.SELECT)) {
			arraySort = app.getArgParam(0).getCCTerm().getFlatTerm().getSort();
			value = app;
		} else if (name.equals(SMTLIBConstants.CONST)) {
			arraySort = app.getFlatTerm().getSort();
			value = app.getArgParam(0);
		} else {
			return;
		}
		addClashMember(slots, new ClashKey(arraySort, POS_ARRAY_ELEMENT), value);
	}

	/**
	 * Add one member to its clash slot, filtering to numeric, LA-valued members (see {@link #getNumericClashSlots}).
	 */
	private static void addClashMember(final Map<ClashKey, List<CCParameter>> slots, final ClashKey key,
			final CCParameter arg) {
		if (!arg.getCCTerm().getFlatTerm().getSort().isNumericSort()) {
			return;
		}
		if (arg.getRepresentative().getSharedTerm() == null) {
			return;
		}
		List<CCParameter> members = slots.get(key);
		if (members == null) {
			members = new ArrayList<>();
			slots.put(key, members);
		}
		members.add(arg);
	}

	/**
	 * Insert a Compare trigger that will be activated as soon as the two given
	 * values are equal. It is inserted into the pair hash tables and all
	 * intermediate pair infos, keyed on the offset between the two base terms
	 * (mirroring {@link #insertEqualityEntry}). The two values may already be in
	 * the same congruence class at a different offset; the trigger is then parked
	 * in the merge-boundary pair info, which becomes live again when the merge is
	 * undone.
	 *
	 * @param lhs     the first value.
	 * @param rhs     the second value.
	 * @param trigger the Compare trigger.
	 */
	public void insertCompareTrigger(final CCParameter lhs, final CCParameter rhs, final CompareTrigger trigger) {
		assert !lhs.sameValueAs(rhs);
		assert !trigger.inList();
		CCTerm t1 = lhs.getCCTerm();
		CCTerm t2 = rhs.getCCTerm();
		// The trigger fires when value(lhs) == value(rhs), i.e. value(t1) - value(t2) == offset.
		Rational offset = rhs.getOffset().sub(lhs.getOffset());
		while (true) {
			// make t1 the term that was merged before t2 was merged.
			if (t1.mMergeTime > t2.mMergeTime) {
				final CCTerm tmp = t1;
				t1 = t2;
				t2 = tmp;
				offset = offset.negate();
			}

			// if t1 is its own representative, then t2 should also be the representative
			// because of merge time
			if (t1.mRep == t1) {
				assert t2.mRep == t2;
				// Insert this entry into the pair hash, create it if necessary.
				CCTermPairHash.Info info = mPairHash.getInfo(t1, t2, offset);
				if (info == null) {
					info = new CCTermPairHash.Info(t1, t2, offset);
					mPairHash.add(info);
				}
				info.mCompareTriggers.prependIntoJoined(trigger, true);
				break;
			}

			// find the pair info entry in the pair info list of t1 or create a new one.
			// isLast is set if t1 was merged with t2; in this case the compare trigger
			// lists were not joined.
			final boolean isLast = t1.mRep == t2;
			boolean found = false;
			for (final CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
				// assert (!info.eqlits.isEmpty());
				if (pentry.mOther == t2 && pentry.getOffsetToOther().equals(offset)) {
					info.mCompareTriggers.prependIntoJoined(trigger, isLast);
					found = true;
					break;
				}
			}
			if (!found) {
				// we need to create a new entry.
				final CCTermPairHash.Info info = new CCTermPairHash.Info(t1, t2, offset);
				info.mRhsEntry.unlink();
				info.mCompareTriggers.prependIntoJoined(trigger, isLast);
			}
			if (isLast) {
				break;
			}
			// walk t1 up to its representative; value(t1) - value(t1.mRep) = t1.mOffsetToRep - t1.mRep.mOffsetToRep
			offset = offset.sub(t1.getOffsetToRep()).add(t1.mRep.getOffsetToRep());
			t1 = t1.mRep;
		}
	}

	/**
	 * Remove a given Compare trigger.
	 */
	public void removeCompareTrigger(final CompareTrigger trigger) {
		CCTerm t1 = trigger.getLhs().getCCTerm();
		CCTerm t2 = trigger.getRhs().getCCTerm();
		if (!mAllTerms.contains(t1) || !mAllTerms.contains(t2)) {
			return; // FIXME This is a workaround for the problem that pop() first removes terms,
					// then triggers, as it
			// is executed for CClosure first. Then this method can be called for a trigger
			// where the
			// corresponding terms have already been removed.
		}
		Rational offset = trigger.getRhs().getOffset().sub(trigger.getLhs().getOffset());
		while (true) {
			// make t1 the term that was merged before t2 was merged.
			if (t1.mMergeTime > t2.mMergeTime) {
				final CCTerm tmp = t1;
				t1 = t2;
				t2 = tmp;
				offset = offset.negate();
			}

			// if t1 is its own representative, then t2 should also be the representative
			// because of merge time
			if (t1.mRep == t1) {
				assert t2.mRep == t2;
				final CCTermPairHash.Info info = mPairHash.getInfo(t1, t2, offset);
				assert info != null;
				info.mCompareTriggers.undoPrependIntoJoined(trigger, true);
				break;
			}

			// find the pair info entry in the pair info list of t1.
			// isLast is set if t1 was merged with t2; in this case the compare trigger
			// lists were not joined.
			final boolean isLast = t1.mRep == t2;
			boolean found = false;
			for (final CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
				// assert (!info.eqlits.isEmpty());
				if (pentry.mOther == t2 && pentry.getOffsetToOther().equals(offset)) {
					info.mCompareTriggers.undoPrependIntoJoined(trigger, isLast);
					found = true;
					break;
				}
			}
			assert found;
			if (isLast) {
				break;
			}
			offset = offset.sub(t1.getOffsetToRep()).add(t1.mRep.getOffsetToRep());
			t1 = t1.mRep;
		}
	}

	/**
	 * Insert a signature backref into the given term. This handles terms that are
	 * not the representative and adds the backref to all relevant lists.
	 *
	 * @param term    the ccterm to insert the backref into.
	 * @param backref the backref to insert.
	 */
	public void addSignatureBackRef(CCTerm arg, final SignatureBackRef backref) {
		while (arg != arg.mRep) {
			arg.mSignatureBackRefs.prependIntoJoined(backref, false);
			arg = arg.mRep;
		}
		arg.mSignatureBackRefs.prependIntoJoined(backref, true);
	}

	/**
	 * Remove a signature backref from the given term. This handles terms that are
	 * not the representative and adds the backref to all relevant lists.
	 *
	 * @param term    the ccterm to remove the backref from.
	 * @param backref the backref to remove.
	 */
	public void removeSignatureBackRef(CCTerm arg, final SignatureBackRef backref) {
		while (arg != arg.mRep) {
			arg.mSignatureBackRefs.prepareRemove(backref);
			arg = arg.mRep;
		}
		backref.removeFromList();
	}

	/**
	 * Insert a Reverse trigger that will be activated as soon as a new function
	 * application of the given function symbol with a given argument value at a
	 * given position exists.
	 *
	 * @param fSym    the function symbol.
	 * @param arg     the argument value the new term should contain; must equal {@code trigger.getArgument()}.
	 * @param argPos  the position of this argument.
	 * @param trigger the Reverse trigger.
	 */
	public void insertReverseTrigger(final FunctionSymbol sym, final CCParameter arg, final int argPos,
			final ReverseTrigger trigger) {
		assert trigger.mSignatureTrigger == null;
		final MasterReverseTrigger masterTrigger = MasterReverseTrigger.of(this, sym, argPos);
		final ReverseTriggerTrigger reverseTriggerTrigger = new ReverseTriggerTrigger(masterTrigger, trigger);
		addSignature(reverseTriggerTrigger);
		trigger.mSignatureTrigger = reverseTriggerTrigger;
	}

	/**
	 * Insert a Reverse trigger that will be activated as soon as a new function
	 * application of the given function symbol exists.
	 *
	 * @param fSym    the function symbol.
	 * @param trigger the Reverse trigger.
	 */
	public void insertFindTrigger(final FunctionSymbol sym, final ReverseTrigger trigger) {
		final FindTriggerTrigger findTriggerTrigger = new FindTriggerTrigger(trigger);
		addSignature(findTriggerTrigger);
		trigger.mSignatureTrigger = findTriggerTrigger;
	}

	/**
	 * Remove a given Reverse trigger.
	 */
	public void removeReverseTrigger(final ReverseTrigger trigger) {
		final SignatureTrigger sigTrigger = trigger.mSignatureTrigger;
		removeSignature(sigTrigger);
	}

	public void addSignature(SignatureTrigger signatureTrigger) {
		signatureTrigger.addBackrefs(this);
		mSignatureTodo.append(signatureTrigger);
	}

	private boolean undoContainsInfoFor(SignatureTrigger signatureTrigger) {
		for (final UndoInfo undoInfo : mUndoStack) {
			if (undoInfo instanceof TriggerMergeUndoEntry) {
				final TriggerMergeUndoEntry triggerInfo = (TriggerMergeUndoEntry) undoInfo;
				if (triggerInfo.mMergedTrigger == signatureTrigger) {
					return true;
				}
				if (triggerInfo.mPreviousTrigger == signatureTrigger) {
					getLogger().debug("Trigger still on Undo: %d %s %s", signatureTrigger.hashCode(), signatureTrigger,
							undoInfo);
					return true;
				}
			}
		}
		return false;
	}

	public void removeSignature(SignatureTrigger signatureTrigger) {
		// assert !undoContainsInfoFor(signatureTrigger);
		if (!signatureTrigger.unmerge(this)) {
			if (signatureTrigger.inList()) {
				signatureTrigger.removeFromList();
				assert mSignatureTriggers.get(signatureTrigger) != signatureTrigger;
			} else {
				assert mSignatureTriggers.get(signatureTrigger) == signatureTrigger;
				mSignatureTriggers.remove(signatureTrigger);
			}
		} else {
			assert false;
		}
		signatureTrigger.removeBackrefs(this);
	}

	public void addSignatureHash(SignatureTrigger signatureTrigger) {
		final SignatureTrigger mergeTrigger = mSignatureTriggers.get(signatureTrigger);
		if (mergeTrigger != null) {
			if (mergeTrigger != signatureTrigger) {
				mergeTrigger.merge(this, signatureTrigger);
				mUndoStack.push(new TriggerMergeUndoEntry(mergeTrigger, signatureTrigger));
			}
		} else {
			mSignatureTriggers.put(signatureTrigger, signatureTrigger);
		}
	}

	public void removeSignatureHash(SignatureTrigger signatureTrigger) {
		if (mSignatureTriggers.get(signatureTrigger) == signatureTrigger) {
			final SignatureTrigger prev = mSignatureTriggers.remove(signatureTrigger);
			assert prev == signatureTrigger;
		}
	}

	/**
	 * Find the representative value for the given term. This function does not
	 * create new terms. If there is no equivalent CCTerm, it returns null. If a
	 * term that is congruent to the given term already exists, it will return the
	 * value of this congruent term, canonicalized as the class representative plus
	 * the value's offset to it.
	 *
	 * @param term The term which a representative is searched for.
	 * @return The representative value, or null if no congruent term exists in the
	 *         CClosure.
	 */
	public CCParameter getCCParamRep(final Term term) {
		final Rational constant = mClausifier.getTermConstant(term);
		final Term offsetFree = constant.equals(Rational.ZERO) ? term : mClausifier.getOffsetFreeTerm(term);
		if (mAnonTerms.containsKey(offsetFree)) {
			final CCTerm ccTerm = mAnonTerms.get(offsetFree);
			return CCParameter.of(ccTerm.getRepresentative(), ccTerm.getOffsetToRep().add(constant));
		}
		if (offsetFree instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) offsetFree;
			final FunctionSymbol funcSym = at.getFunction();
			final Term[] params = at.getParameters();
			final CCParameter[] argReps = new CCParameter[params.length];
			for (int i = 0; i < params.length; i++) {
				argReps[i] = getCCParamRep(params[i]);
				if (argReps[i] == null) {
					return null;
				}
			}
			final SignatureTrigger sig = new SignatureTrigger(funcSym, argReps);
			final CongruenceTrigger congTrigger = (CongruenceTrigger) mSignatureTriggers.get(sig);
			if (congTrigger != null) {
				final CCAppTerm app = congTrigger.getApp();
				return CCParameter.of(app.getRepresentative(), app.getOffsetToRep().add(constant));
			}
		}
		return null;
	}

	/**
	 * For two given values, check if the equality is set.
	 *
	 * @return true if the values are currently equal (same congruence class at the same offset), false otherwise.
	 */
	public boolean isEqSet(final CCParameter first, final CCParameter second) {
		return first.sameValueAs(second);
	}

	/**
	 * For two given values, check if the disequality is known to hold, either because a disequality literal is set or
	 * because the values are in the same congruence class at different offsets (so they provably differ by a non-zero
	 * constant).
	 *
	 * @return true if the disequality holds, false otherwise.
	 */
	public boolean isDiseqSet(final CCParameter first, final CCParameter second) {
		final CCTerm firstRep = first.getRepresentative();
		final CCTerm secondRep = second.getRepresentative();
		final Rational offset = second.getOffsetToRep().sub(first.getOffsetToRep());
		if (firstRep == secondRep) {
			// Same class: the value difference is the known constant offset.
			return !offset.equals(Rational.ZERO);
		}
		// A diseq disproves value(first) == value(second), i.e. value(firstRep) - value(secondRep) ==
		// second.mOffsetToRep - first.mOffsetToRep.
		final CCTermPairHash.Info diseqInfo = mPairHash.getInfo(firstRep, secondRep, offset);
		return diseqInfo != null && diseqInfo.mDiseq != null;
	}

	/**
	 * Insert an equality entry into the pair hash table and all pair infos of the
	 * intermediate representatives.
	 *
	 * @param t1      one side of the equality.
	 * @param t2      the other side of the equality
	 * @param eqentry the equality entry that should be inserted into the pair
	 *                infos.
	 */
	public void insertEqualityEntry(CCTerm t1, CCTerm t2, Rational offset, final CCEquality.Entry eqentry) {
		// offset == value(t1) - value(t2)
		while (true) {
			// make t1 the term that was merged before t2 was merged.
			if (t1.mMergeTime > t2.mMergeTime) {
				final CCTerm tmp = t1;
				t1 = t2;
				t2 = tmp;
				offset = offset.negate();
			}

			// if t1 is its own representative, then t2 should also be the representative
			// because of merge time
			if (t1.mRep == t1) {
				assert t2.mRep == t2;
				// Insert this entry into the pair hash, create it if necessary.
				CCTermPairHash.Info info = mPairHash.getInfo(t1, t2, offset);
				if (info == null) {
					info = new CCTermPairHash.Info(t1, t2, offset);
					mPairHash.add(info);
				}
				info.mEqlits.prependIntoJoined(eqentry, true);
				break;
			}

			// find the pair info entry in the pair info list of t1 or create a new one.
			// isLast is set if t1 was merged with t2; in this case the equality entry lists
			// were not joined.
			final boolean isLast = t1.mRep == t2;
			boolean found = false;
			for (final CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
				// assert (!info.eqlits.isEmpty());
				if (pentry.mOther == t2 && pentry.getOffsetToOther().equals(offset)) {
					info.mEqlits.prependIntoJoined(eqentry, isLast);
					found = true;
					break;
				}
			}
			if (!found) {
				// we need to create a new entry.
				final CCTermPairHash.Info info = new CCTermPairHash.Info(t1, t2, offset);
				info.mRhsEntry.unlink();
				info.mEqlits.prependIntoJoined(eqentry, isLast);
			}
			if (isLast) {
				break;
			}
			// walk t1 up to its representative; value(t1) - value(t1.mRep) = t1.mOffsetToRep - t1.mRep.mOffsetToRep
			offset = offset.sub(t1.getOffsetToRep()).add(t1.mRep.getOffsetToRep());
			t1 = t1.mRep;
		}
	}

	public CCEquality createCCEquality(final int stackLevel, final CCTerm t1, final CCTerm t2) {
		return createCCEquality(stackLevel, t1, t2, Rational.ZERO);
	}

	/**
	 * Create a CCEquality stating {@code value(t1) == value(t2) + offset}.
	 */
	public CCEquality createCCEquality(final int stackLevel, CCTerm t1, CCTerm t2, Rational offset) {
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
			offset = offset.negate();
		}
		eq = new CCEquality(stackLevel, t1, t2, offset);
		insertEqualityEntry(t1, t2, offset, eq.getEntry());
		getEngine().addAtom(eq);

		assert t1.invariant();
		assert t2.invariant();
		assert t1.pairHashValid(this);
		assert t2.pairHashValid(this);

		if (t1.mRepStar == t2.mRepStar) {
			// The two terms are already in the same class. The equality is implied true only if the offset matches the
			// offset they already have; otherwise it is implied false but we leave it for the SAT solver (setLiteral
			// detects the conflict if it is ever set true).
			final Rational existingDiff = t1.getOffsetToRep().sub(t2.getOffsetToRep());
			if (existingDiff.equals(offset)) {
				if (getLogger().isDebugEnabled()) {
					getLogger().debug("CC-Prop: " + eq + " repStar: " + t1.mRepStar);
				}
				mPendingLits.add(eq);
				mRecheckOnBacktrackLits.add(eq);
			}
		} else {
			// value(t1Rep) - value(t2Rep) under the equality
			final Rational repOffset = offset.sub(t1.getOffsetToRep()).add(t2.getOffsetToRep());
			final CCTermPairHash.Info repInfo = mPairHash.getInfo(t1.mRepStar, t2.mRepStar, repOffset);
			final CCEquality diseq = repInfo == null ? null : repInfo.mDiseq;
			if (diseq != null) {
				if (getLogger().isDebugEnabled()) {
					getLogger().debug("CC-Prop: " + eq.negate() + " diseq: " + diseq);
				}
				eq.setDiseqReason(diseq);
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
	public Clause finalCheck() {
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
		// Lazy explanation: the reason for a propagated disequality is computed on demand in getUnitClause /
		// computeAntiCycle (which no longer mutates the graph and orients the diseq from eq.mDiseqOrientation).
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
			return computeAntiCycle(eq.mDiseqReason, eq.mDiseqOrientation, eq);
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
	 * Move a signature trigger from the global signature hashes to the todo list.
	 *
	 * @param signatureTrigger
	 * @return true, if the signature was added, false if it already was in the
	 */
	public void moveToSignatureTodo(SignatureTrigger signatureTrigger) {
		if (!signatureTrigger.inList()) {
			mSignatureTodo.append(signatureTrigger);
			removeSignatureHash(signatureTrigger);
		}
	}

	/**
	 * Push the smaller class's back-ref list onto the signature todo. Called from
	 * merge when merging two classes; the actual rehash and trigger merge happen at
	 * checkpoint.
	 *
	 * @param oldRep   the former representative of the smaller class (src).
	 * @param newRep   the new representative of the smaller class (dest).
	 * @param backRefs the list of (signature, listIndex, trigger) back-refs from
	 *                 that representative.
	 */
	void rehashSignatures(final CCTerm oldRep, final CCTerm newRep, final Rational offsetDelta,
			final SimpleList<SignatureBackRef> backRefs) {
		for (final SignatureBackRef backRef : backRefs) {
			final SignatureTrigger signatureTrigger = backRef.getSignatureTrigger();
			signatureTrigger.rehash(this, backRef.getArgPosition(), oldRep, newRep, offsetDelta);
		}
	}

	/**
	 * Find the MergeUndoInfo on the undo stack for the given old representative.
	 * Used at checkpoint to attach signature-undo entries.
	 */
	MergeUndoInfo findMergeUndoInfo(final CCTerm oldRep) {
		for (final UndoInfo info : mUndoStack) {
			if (info instanceof MergeUndoInfo && ((MergeUndoInfo) info).getOldRep() == oldRep) {
				return (MergeUndoInfo) info;
			}
		}
		return null;
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
			} else {
				// The terms are already in the same class. Asserting the equality is a conflict if their actual offset
				// differs from the offset claimed by the equality (e.g. asserting x == x + 1). The conflict clause is
				// {¬eq, ¬path}: eq is true, so ¬eq is false, and the path literals are all true, so the clause is
				// falsified. (computeCycle would put eq positively and yield a satisfied clause.)
				final Rational existingDiff = eq.getLhs().getOffsetToRep().sub(eq.getRhs().getOffsetToRep());
				if (!existingDiff.equals(eq.getOffset())) {
					return computeAntiCycle(null, false, eq);
				}
			}
		} else {
			final CCTerm left = eq.getLhs().mRepStar;
			final CCTerm right = eq.getRhs().mRepStar;

			/* Check for conflict */
			if (left == right) {
				// They are in the same class. The disequality is a conflict only if they are equal at exactly the
				// offset the equality claims; if their actual offset differs, the disequality already holds and there
				// is nothing to separate.
				final Rational existingDiff = eq.getLhs().getOffsetToRep().sub(eq.getRhs().getOffsetToRep());
				if (existingDiff.equals(eq.getOffset())) {
					return computeCycle(eq);
				}
			} else {
				separate(left, right, eq);
			}
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
		final CCTermPairHash.Info info = mPairHash.getInfo(lhs, rhs, repOffset(diseq));
		if (info.mDiseq != null) {
			/*
			 * The two classes are already separated at this offset by another asserted disequality, e.g. by an atom
			 * between other members of the two classes; this happens when a merge brings the two atoms onto the same
			 * representative pair and the second one is then set false by the arithmetic solver (so it has no diseq
			 * reason to short-circuit on above). This literal adds no information: keep the recorded disequality and
			 * skip the propagation, which it has already done. Overwriting it would be wrong, since undoSep() would
			 * then drop the separation on backtracking while the other literal is still asserted. The recorded
			 * disequality outlives this one, as it was asserted earlier.
			 */
			return;
		}

		mUndoStack.push(new SepUndoInfo(diseq));
		info.mDiseq = diseq;
		/* Propagate inequalities */
		for (final CCEquality.Entry eqentry : info.mEqlits) {
			final CCEquality eq = eqentry.getCCEquality();
			// eq cannot be decided true here: that would merge lhs and rhs, contradicting that they are distinct
			// representatives. With offset equalities it may already be decided false (propagated by an earlier
			// offset merge); such an eq keeps its existing reason and is simply skipped.
			assert eq.getDecideStatus() != eq || eq == diseq;
			if (eq.getDecideStatus() == null) {
				eq.setDiseqReason(diseq);
				addPending(eq.negate());
			}
		}
	}

	/**
	 * The offset of an equality as seen between the representatives of its two sides, i.e.
	 * {@code value(eq.getLhs().mRepStar) - value(eq.getRhs().mRepStar)} implied by the equality.
	 */
	private static Rational repOffset(final CCEquality eq) {
		return eq.getOffset().sub(eq.getLhs().getOffsetToRep()).add(eq.getRhs().getOffsetToRep());
	}

	private void undoSep(final CCEquality atom) {
		final CCTermPairHash.Info destInfo =
				mPairHash.getInfo(atom.getLhs().mRepStar, atom.getRhs().mRepStar, repOffset(atom));
		assert destInfo != null && destInfo.mDiseq == atom;
		destInfo.mDiseq = null;
	}

	public Clause computeCycle(final CCEquality eq) {
		final CongruencePath congPath = new CongruencePath(this);
		final Clause res = congPath.computeCycle(eq, isProofGenerationEnabled());
		assert (res.getSize() != 2 || res.getLiteral(0).negate() != res.getLiteral(1));
		return res;
	}

	/**
	 * Compute the conflict clause for a shared-term clash detected during a merge (the merged values of the two classes'
	 * shared terms are provably distinct, e.g. an integer shared term forced to a non-integer value). See
	 * {@link CongruencePath#computeMergeConflictCycle}.
	 */
	public Clause computeSharedConflictCycle(final CCTerm lshared, final CCTerm rshared, final CCTerm lhs,
			final CCTerm rhsTerm, final CCEquality reason, final Rational bridgeOff) {
		return new CongruencePath(this).computeMergeConflictCycle(lhs, rhsTerm, bridgeOff, reason, lshared, rshared,
				null, isProofGenerationEnabled());
	}

	/**
	 * Compute the conflict clause when a merge of two classes is forbidden by a disequality {@code diseq} registered
	 * between them at exactly the merge offset. {@code srcEnd}/{@code destEnd} are the two sides of {@code diseq},
	 * oriented into the source class (reachable from {@code lhs}) and destination class (reachable from {@code rhsTerm});
	 * the path crosses the freshly added (not-yet-united) merge bridge, so it is built as two single-class halves. See
	 * {@link CongruencePath#computeMergeConflictCycle}.
	 */
	public Clause computeMergeDiseqCycle(final CCTerm srcEnd, final CCTerm destEnd, final CCTerm lhs,
			final CCTerm rhsTerm, final CCEquality reason, final Rational bridgeOff, final CCEquality diseq) {
		return new CongruencePath(this).computeMergeConflictCycle(lhs, rhsTerm, bridgeOff, reason, srcEnd, destEnd,
				diseq, isProofGenerationEnabled());
	}

	/**
	 * Compute a conflict explaining incompatibility of eq and diseq. Called when
	 * asserting eq would create a conflict on merge with the given diseq.
	 */
	public Clause computeAntiCycle(final CCEquality diseq, final boolean diseqOrientation, final CCEquality eq) {
		final CCTerm lhsDiseq;
		final CCTerm rhsDiseq;
		if (diseq == null) {
			// No separating disequality (e.g. x != x+5): the two sides are in the same class at a deviating offset.
			assert eq.getLhs().mRepStar == eq.getRhs().mRepStar;
			assert !eq.getLhs().getOffsetToRep().sub(eq.getRhs().getOffsetToRep()).equals(eq.getOffset());
			lhsDiseq = eq.getLhs();
			rhsDiseq = eq.getLhs();
		} else {
			// A concrete disequality separates eq's two sides. This works whether they are
			// still in different classes or were
			// merged later: orient diseq from eq's stored orientation (live reps can no
			// longer tell the two sides apart after
			// a merge), then build the two single-class halves and stitch them across the
			// eq bridge.
			lhsDiseq = diseqOrientation ? diseq.getLhs() : diseq.getRhs();
			rhsDiseq = diseqOrientation ? diseq.getRhs() : diseq.getLhs();
		}
		return new CongruencePath(this).computeMergeConflictCycle(eq.getLhs(), eq.getRhs(), eq.getOffset(), eq, lhsDiseq,
				rhsDiseq, diseq, isProofGenerationEnabled());
	}

	/**
	 * Compute the conflict clause when a congruence merge finds its two function applications already in the same
	 * congruence class at an offset different from the zero offset that congruence implies (e.g. f(x) and f(y) are
	 * congruent but the class already records f(x) = f(y) + k for k != 0). A degenerate
	 * {@link CongruencePath#computeMergeConflictCycle}: the bridge is the congruence ({@code reason == null}, justified by
	 * the argument equalities) and the endpoints coincide ({@code srcEnd == destEnd == first}), so the destination half
	 * is the existing class path from {@code second} back to {@code first} and the trivial diseq
	 * {@code (first@0, first@existingDiff)} is EQ-discharged.
	 */
	public Clause computeCongruenceAntiCycle(final CCAppTerm first, final CCAppTerm second) {
		assert first.getRepresentative() == second.getRepresentative();
		assert first.getFunctionSymbol() == second.getFunctionSymbol();
		return new CongruencePath(this).computeMergeConflictCycle(first, second, Rational.ZERO, null, first, first, null,
				isProofGenerationEnabled());
	}

	/**
	 * Compute the earliest decide level at which the path between lhs and rhs
	 * exists. There must be a path, i.e.
	 * {@code lhs.getRepresentative() == rhs.getRepresentative()}.
	 *
	 * @param lhs the start of the path
	 * @param rhs the end of the path
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
			if (left.mRepStar == right.mRepStar) {
				// Offset disequality: the two sides are in the same class at an offset different from eq's, so eq is
				// false with no separating disequality atom (mDiseqReason stays null; the path is the reason).
				assert !left.getOffsetToRep().sub(right.getOffsetToRep()).equals(eq.getOffset());
				return true;
			}
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

	public CCEquality createEquality(final CCParameter t1, final CCParameter t2, final boolean createLAEquality) {
		// Use the structural offset (CCParameter.getOffset()), so the created literal is keyed like the original
		// clause literals (see CCProofGenerator.collectClauseLiterals). The dynamic getOffsetToRep() must not be used:
		// the two parameters need not be in the same congruence class when this literal is created.
		return createEquality(t1.getCCTerm(), t2.getCCTerm(), t2.getOffset().sub(t1.getOffset()), createLAEquality);
	}

	/**
	 * Create (and propagate) an equality {@code value(t1) == value(t2) + offset} between two shared terms. The offset is
	 * encoded into the right-hand term ({@code t2 + offset}) so that the resulting CCEquality carries the offset and the
	 * linked LAEquality carries the matching constant. With a zero offset this is the classic shared-term equality.
	 */
	public CCEquality createEquality(final CCTerm t1, final CCTerm t2, final Rational offset,
			final boolean createLAEquality) {
		assert t1 != t2 || !offset.equals(Rational.ZERO);
		final Term lhsTerm = t1.getFlatTerm();
		Term rhsTerm = t2.getFlatTerm();
		if (!offset.equals(Rational.ZERO)) {
			// Build the flattened polynomial term t2 + offset. A nested (+ t2 offset) would not be re-parsed
			// correctly by Polynomial when t2 is itself a normalized sum (the inner sum is treated as one monomial).
			rhsTerm = mClausifier.addConstantToTerm(rhsTerm, offset);
		}
		final EqualityProxy ep = mClausifier.createEqualityProxy(lhsTerm, rhsTerm,
				SourceAnnotation.EMPTY_SOURCE_ANNOT);
		if (ep == EqualityProxy.getFalseProxy()) {
			return null;
		}
		if (!createLAEquality) {
			final Literal res = ep.getLiteral(SourceAnnotation.EMPTY_SOURCE_ANNOT);
			if (res instanceof CCEquality) {
				final CCEquality eq = (CCEquality) res;
				if ((eq.getLhs() == t1 && eq.getRhs() == t2) || (eq.getLhs() == t2 && eq.getRhs() == t1)) {
					return eq;
				}
			}
		}
		// t1 and t2 are the offset-free CC nodes; pass them with this call's offset (which may differ from the proxy's
		// canonical offset for a scaled equivalent) rather than round-tripping through the synthesized rhsTerm.
		// This path creates an LAEquality, so it must only be taken for numeric equalities; a non-numeric equality
		// always matches the literal above (a mismatch would indicate a stale atom referencing removed CCTerms).
		assert lhsTerm.getSort().isNumericSort();
		return ep.createCCEquality(t1, t2, offset);
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
					if (!t2.getOffsetToRep().equals(Rational.ZERO)) {
						sb.append("[+").append(t2.getOffsetToRep()).append(']');
					}
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
				// don't check symmetric cases: skip all terms in the inner loop up to and
				// including the term t1.
				// Thus we check exactly the pairs (t1,t2) where t1 occurs (strictly) before t2
				// in mAllTerms.
				if (skip) {
					if (t1 == t2) {
						skip = false;
					}
					continue;
				}
				if (t1.getRepresentative() != t2.getRepresentative() && t2 instanceof CCAppTerm) {
					final CCAppTerm a2 = (CCAppTerm) t2;
					if (a1.getFunctionSymbol() == a2.getFunctionSymbol()) {
						final int arity = a1.mArgs.length;
						int i;
						for (i = 0; i < arity; i++) {
							// congruent requires the arguments to have the same value, i.e. same representative AND
							// same offset (offset-free arguments are compared as plain representatives).
							if (!a1.getArgParam(i).sameValueAs(a2.getArgParam(i))) {
								break;
							}
						}
						if (i == arity) {
							getLogger().fatal("Should be congruent: " + t1 + " and " + t2);
							return false;
						}
					}
				}
			}
		}
		return true;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		logger.info("CCTimes: iE " + mInvertEdgeTime / 1000000 + " eq " + mEqTime / 1000000 + " cc " + mCcTime / 1000000
				+ " setRep " + mSetRepTime / 1000000 + " sh " + mSigHashTime / 1000000);
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
		 * If a literal was propagated when it was created it may not be on the right
		 * decision level. After backtracking we may need to propagate these literals
		 * again, if they are still implied by the CC graph. Here we go through the list
		 * of all such literals and check if we ned to propagate them again.
		 */
		final ArrayQueue<Literal> newRecheckOnBacktrackLits = new ArrayQueue<>();
		for (final Literal l : mRecheckOnBacktrackLits) {
			final CCEquality eq = (CCEquality) l.getAtom();
			if (eq.getDecideStatus() != null) {
				/* We did not yet backtrack the literal; keep it for later */
				newRecheckOnBacktrackLits.add(l);
				/*
				 * It may have an LAEquality that was backtracked. Then we need to propagate the
				 * LAEquality.
				 */
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
				// implied true only if the terms are in the same class at the equality's offset
				repropagate = (lhs == rhs
						&& eq.getLhs().getOffsetToRep().sub(eq.getRhs().getOffsetToRep()).equals(eq.getOffset()));
			} else {
				final CCTermPairHash.Info info = mPairHash.getInfo(lhs, rhs, repOffset(eq));
				final CCEquality diseq = info == null ? null : info.mDiseq;
				if (diseq != null) {
					eq.setDiseqReason(diseq);
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
		return null;
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
		getLogger().debug("addPendingCongruence: %s %s", first, second);
		mPendingCongruences.add(new SymmetricPair<>(first, second));
	}

	/**
	 * Add all pending congruences to the CC graph. We do not merge congruences
	 * immediately but wait for checkpoint. Then this method is called to merge
	 * congruent function applications.
	 *
	 * @param checked if true, congruences are only applied if they still hold.
	 * @return A conflict clause if a conflict was found, null otherwise.
	 */
	@SuppressWarnings("unused")
	private Clause buildCongruence() {
		while (!mSignatureTodo.isEmpty() || !mPendingCongruences.isEmpty()) {
			final long time = System.nanoTime();
			while (!mSignatureTodo.isEmpty()) {
				final SignatureTrigger trigger = mSignatureTodo.removeFirst();
				addSignatureHash(trigger);
			}
			mSigHashTime += System.nanoTime() - time;
			SymmetricPair<CCAppTerm> cong;
			while ((cong = mPendingCongruences.poll()) != null) {
				getLogger().debug("PC %s", cong);
				final CCAppTerm lhs = cong.getFirst();
				final CCAppTerm rhs = cong.getSecond();
				assert lhs.getFunctionSymbol() == rhs.getFunctionSymbol();
				final Clause res = lhs.merge(this, rhs, null);
				if (res != null) {
					getLogger().debug("buildCongruence: conflict %s", res);
					return res;
				}
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
			} else if (top instanceof SepUndoInfo) {
				final CCEquality diseq = ((SepUndoInfo) top).getDiseq();
				undoSep(diseq);
			} else if (top instanceof TriggerMergeUndoEntry) {
				final TriggerMergeUndoEntry signatureUndo = (TriggerMergeUndoEntry) top;
				signatureUndo.getMergedTrigger().undoMerge(this, signatureUndo.getPreviousTrigger());
				mSignatureTodo.append(signatureUndo.getPreviousTrigger());
			} else {
				throw new AssertionError("Unknown undo info type: " + top);
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
			removeCCEquality(cceq.getLhs(), cceq.getRhs(), cceq.getOffset(), cceq);
		}
	}

	private void removeCCEquality(CCTerm t1, CCTerm t2, Rational offset, final CCEquality eq) {
		// TODO Need test for this!!!
		// offset == value(t1) - value(t2)
		if (t1.mMergeTime > t2.mMergeTime) {
			final CCTerm tmp = t1;
			t1 = t2;
			t2 = tmp;
			offset = offset.negate();
		}

		if (t1.mRep == t1) {
			assert t2.mRep == t2;
			final CCTermPairHash.Info info = mPairHash.getInfo(t1, t2, offset);
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
				if (pentry.mOther == t2 && pentry.getOffsetToOther().equals(offset)) {
					info.mEqlits.prepareRemove(eq.getEntry());
					found = true;
					break;
				}
			}
			assert found;
			if (isLast) {
				eq.getEntry().removeFromList();
			} else {
				removeCCEquality(t1.mRep, t2, offset.sub(t1.getOffsetToRep()).add(t1.mRep.getOffsetToRep()), eq);
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
			final CCAppTerm appTerm = (CCAppTerm) t;
			removeSignature(appTerm.mCongTrigger);
			removeSignature(appTerm.mFindTrigger);
			if (appTerm.mReverseTriggers != null) {
				// remove the reverse trigger signatures created for this application (all merges are already
				// undone at pop time, so each application entry is back in its own signature).
				for (final ReverseTriggerTrigger trigger : appTerm.mReverseTriggers) {
					removeSignature(trigger);
				}
				appTerm.mReverseTriggers = null;
			}
		}
	}

	@Override
	public void backtrackAll() {
		assert mDecideLevelToUndoStackSize.isEmpty();
		backtrackStack(0);
		mPendingLits.clear();
		mRecheckOnBacktrackLits.clear();
		mPendingCongruences.clear();
	}

	@Override
	public void pop() {
		assert mDecideLevelToUndoStackSize.isEmpty();
		assert mUndoStack.isEmpty();
		// assert mSignatureTodo.isEmpty();
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

	/**
	 * Record for undoing a trigger merge: undo the merge on mMergedTrigger and put
	 * mPreviousTrigger back on {@link #mSignatureTodo}, so the next checkpoint
	 * re-inserts it into {@link #mSignatureTriggers}. The same key object then
	 * hashes back to its old bucket, since the merge undo also restored the
	 * representatives and offsets its hash is computed from.
	 */
	static final class TriggerMergeUndoEntry extends UndoInfo {
		final SignatureTrigger mMergedTrigger;
		final SignatureTrigger mPreviousTrigger;

		TriggerMergeUndoEntry(final SignatureTrigger mergedTrigger, final SignatureTrigger previousTrigger) {
			mMergedTrigger = mergedTrigger;
			mPreviousTrigger = previousTrigger;
		}

		SignatureTrigger getMergedTrigger() {
			return mMergedTrigger;
		}

		SignatureTrigger getPreviousTrigger() {
			return mPreviousTrigger;
		}
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
