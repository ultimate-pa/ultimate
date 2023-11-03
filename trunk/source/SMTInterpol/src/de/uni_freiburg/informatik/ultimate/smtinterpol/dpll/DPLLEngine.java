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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause.WatchList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CuckooHashSet;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * The DPLL engine.
 *
 * @author hoenicke
 *
 */
public class DPLLEngine {
	private final LogProxy mLogger;
	/* Completeness */
	public static final int COMPLETE = 0;
	public static final int INCOMPLETE_QUANTIFIER = 1;
	public static final int INCOMPLETE_THEORY = 2;
	public static final int INCOMPLETE_MEMOUT = 3;
	public static final int INCOMPLETE_UNKNOWN = 4;
	public static final int INCOMPLETE_TIMEOUT = 5;
	public static final int INCOMPLETE_CHECK = 6;
	public static final int INCOMPLETE_CANCELLED = 7;

	private static final String[] COMPLETENESS_STRINGS = { "Complete", "Quantifier in Assertion Stack",
			"Theories with incomplete decision procedure used", "Not enough memory", "Unknown internal error",
			"Sat check timed out", "Incomplete check used", "User requested cancellation" };
	private int mCompleteness;

	/* Incrementality */
	/**
	 * Number of active pushs.
	 */
	private int mPushPopLevel = 0;
	/**
	 * The push/pop recovery data.
	 */
	private final ScopedArrayList<DPLLAtom> mAtomList;
	/**
	 * List of all input clauses. This list should not contain any learned clauses!
	 */
	private final SimpleList<Clause> mClauses = new SimpleList<>();

	/**
	 * Empty clause. This is a cache that speeds up detecting unsatisfiability in
	 * the case our proof does not depend on a newly pushed formula.
	 */
	private Clause mUnsatClause = null;

	/**
	 * The literals assumed in the last check-sat-assuming call.
	 */
	private final Set<Literal> mAssumptionLiterals = new LinkedHashSet<>();

	/* Statistics */
	private int mConflicts, mDecides, mTProps, mProps;
	private int mNumSolvedAtoms, mNumClauses, mNumAxiomClauses;
	SimpleList<Clause> mLearnedClauses = new SimpleList<>();
	private long mPropTime, mPropClauseTime, mExplainTime;
	private long mSetTime, mCheckTime, mBacktrackTime;
	private int mNumRandomSplits;

	private boolean mHasModel;

	double mAtomScale = 1 - 1.0 / Config.ATOM_ACTIVITY_FACTOR;
	double mClsScale = 1 - 1.0 / Config.CLS_ACTIVITY_FACTOR;

	/**
	 * The list of watchers that need to be rechecked. A watcher is added if the
	 * clause was just added, or when backtracking, because the watcher was moved to
	 * the backtrack list of a true literal, or because the watched literal was just
	 * set to false.
	 */
	WatchList mPendingWatcherList = new WatchList();

	/**
	 * The DPLL stack is the stack of all literals that are currently assigned true.
	 * Every decided or propagated literal is added to the DPLL stack and removed on
	 * backtracking. The DPLL stack usually works as a stack, but there are some
	 * exceptions where literals are created and inserted into the middle of the
	 * stack.
	 */
	ArrayList<Literal> mDPLLStack = new ArrayList<>();

	/**
	 * The list of all theories.
	 */
	private ITheory[] mTheories = new ITheory[0];
	private final AtomQueue mAtoms = new AtomQueue();

	private int mCurrentDecideLevel = 0;
	private int mBaseLevel = 0;
	private boolean mPGenabled = false;
	private ScopedHashMap<String, Literal> mAssignments;

	// Random source for the solver.
	private final Random mRandom;

	private final TerminationRequest mCancel;

	public DPLLEngine(final LogProxy logger, final TerminationRequest cancel) {
		mCompleteness = COMPLETE;
		assert logger != null;
		mLogger = logger;
		mAtomList = new ScopedArrayList<>();
		// Benchmark sets the seed...
		mRandom = new Random();
		mCancel = cancel;
	}

	public int getDecideLevel() {
		return mCurrentDecideLevel;
	}

	public void insertPropagatedLiteral(final ITheory t, final Literal lit, final int decideLevel) {
		assert lit.getAtom().mDecideStatus == null;
		assert !mDPLLStack.contains(lit);
		assert !mDPLLStack.contains(lit.negate());
		assert t != null : "Decision in propagation!!!";
		assert checkDecideLevel();
		int stackptr = mDPLLStack.size();
		int level = mCurrentDecideLevel;
		while (level > decideLevel) {
			final DPLLAtom atom = mDPLLStack.get(--stackptr).getAtom();
			if (atom.mExplanation == null) {
				level--;
			}
			atom.mStackPosition++;
		}
		mDPLLStack.add(stackptr, lit);
		final DPLLAtom atom = lit.getAtom();
		// We have to tell the ppStack about this literal. Otherwise it will
		// not be removed on a pop
		mAtomList.add(atom);
		assert !mAtoms.contains(atom);
		atom.mDecideLevel = decideLevel;
		atom.mStackPosition = stackptr;
		atom.mDecideStatus = lit;
		atom.mLastStatus = atom.mDecideStatus;
		atom.mExplanation = t;
		if (decideLevel <= mBaseLevel) {
			/* This atom is now decided once and for all. */
			mNumSolvedAtoms++;
			generateLevel0Proof(lit);
		}
		assert checkDecideLevel();
	}

	public void insertPropagatedLiteralBefore(final ITheory t, final Literal lit, final Literal beforeLit) {
		final DPLLAtom beforeAtom = beforeLit.getAtom();
		assert mDPLLStack.get(beforeAtom.getStackPosition()).getAtom() == beforeAtom;
		assert beforeAtom.mDecideStatus != null;
		assert beforeAtom.getStackPosition() >= 0;
		assert lit.getAtom().mDecideStatus == null;
		assert !mDPLLStack.contains(lit);
		assert !mDPLLStack.contains(lit.negate());
		assert t != null : "Decision in propagation!!!";
		assert checkDecideLevel();
		final int stackptr = beforeAtom.getStackPosition();
		int level = beforeAtom.getDecideLevel();
		if (beforeAtom.mExplanation == null) {
			level--;
		}
		mDPLLStack.add(stackptr, lit);
		for (int i = stackptr + 1; i < mDPLLStack.size(); i++) {
			assert mDPLLStack.get(i).getAtom().getStackPosition() == i - 1;
			mDPLLStack.get(i).getAtom().mStackPosition = i;
		}
		final DPLLAtom atom = lit.getAtom();
		// We have to tell the ppStack about this literal. Otherwise it will
		// not be removed on a pop
		mAtomList.add(atom);
		assert !mAtoms.contains(atom);
		atom.mDecideLevel = level;
		atom.mStackPosition = stackptr;
		atom.mDecideStatus = lit;
		atom.mLastStatus = atom.mDecideStatus;
		atom.mExplanation = t;
		if (level <= mBaseLevel) {
			/* This atom is now decided once and for all. */
			mNumSolvedAtoms++;
			generateLevel0Proof(lit);
		}
		assert checkDecideLevel();
	}

	/**
	 * Propagate unit clauses first in boolean part, then in the theory part.
	 *
	 * @return a conflict clause if a conflict was detected.
	 */
	@SuppressWarnings("unused")
	private Clause propagateInternal() {

		while (true) {
			Clause conflict = propagateTheories();
			if (conflict != null) {
				return conflict;
			}
			final int level = mDPLLStack.size();
			final int numAtoms = mAtoms.size();
			conflict = propagateClauses();
			if (conflict != null) {
				return conflict;
			}
			if (mDPLLStack.size() > level) {
				continue;
			}

			long time = 0;
			if (Config.PROFILE_TIME) {
				time = System.nanoTime();
			}
			mLogger.debug("DPLL: checkpoint");
			for (final ITheory t : mTheories) {
				conflict = t.checkpoint();
				if (conflict != null) {
					return conflict;
				}
			}
			if (Config.PROFILE_TIME) {
				mCheckTime += System.nanoTime() - time;
			}

			conflict = propagateTheories();
			assert !Config.EXPENSIVE_ASSERTS || checkDecideLevel();
			if (conflict != null) {
				return conflict;
			}
			if (mDPLLStack.size() == level && mAtoms.size() == numAtoms) {
				return null;
			}
		}
	}

	private Clause propagateTheories() {
		while (true) {
			boolean changed = false;
			mLogger.debug("DPLL: propagate theories");
			for (final ITheory t : mTheories) {
				Literal propLit = t.getPropagatedLiteral();
				if (propLit != null) {
					do {
						if (propLit.mAtom.mDecideStatus == null) {
							mTProps++;
							if (propLit.mAtom.mExplanation == null) {
								propLit.mAtom.mExplanation = t;
							}
							final Clause conflict = setLiteral(propLit);
							if (conflict != null) {
								for (final Literal lit : conflict.mLiterals) {
									final DPLLAtom atom = lit.getAtom();
									assert atom.mDecideStatus == lit.negate();
								}
								return conflict;
							}
						} else if (propLit.mAtom.mDecideStatus != propLit) {
							final Clause conflict = t.getUnitClause(propLit);
							return conflict;
						}
						propLit = t.getPropagatedLiteral();
					} while (propLit != null);
					changed = true;
				}
			}
			if (!changed) {
				return null;
			}
		}
	}

	/**
	 * Go through the watcher list and check for pending conflict or unit clauses.
	 * This returns early if a literal was propagated. The caller needs to check if
	 * the dpllStack changed to conclude if it has to re-check for theory
	 * propagations.
	 *
	 * @return a conflict clause, null if no conflict was found.
	 */
	private Clause propagateClauses() {
		long time = 0;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime() - mSetTime;
		}

		// logger.info("new set: "+watcherSetList.size());
		nextList: while (!mPendingWatcherList.isEmpty()) {
			final int index = mPendingWatcherList.getIndex();
			Clause clause = mPendingWatcherList.removeFirst();
			/* check if clause was already removed */
			if (clause.mNext == null) {
				continue nextList;
			}
			final Literal[] lits = clause.mLiterals;
			/*
			 * For non-unit clauses we check if the watched literal is set to false. If not,
			 * just put the watcher back on the list. A unit clause has a watcher on a
			 * virtual second literal that is treated as if it were always false. In that
			 * case we don't check if it is still undecided.
			 */
			if (index < lits.length) {
				final Literal myLit = lits[index];
				if (myLit.getAtom().getDecideStatus() != myLit.negate()) {
					/* The watcher is still fine. Put it on the mWatchers list of that literal */
					myLit.mWatchers.append(clause, index);
					continue nextList;
				}
			} else {
				/* this is only for unit clauses */
				assert index == 1 && lits.length == 1;
			}

			/*
			 * myLit is set to false and there are other literals. Check if we can propagate
			 * the other literal, or if there are other undecided or true literals.
			 */
			final Literal otherLit = lits[1 - index];
			final DPLLAtom otherAtom = otherLit.getAtom();
			if (otherAtom.mDecideStatus == otherLit) {
				/*
				 * Other watcher is true, put ourself on the backtrack watcher list.
				 */
				otherAtom.mBacktrackWatchers.append(clause, index);
				continue nextList;
			}
			for (int i = 2; i < lits.length; i++) {
				final Literal lit = lits[i];
				final DPLLAtom atom = lit.getAtom();
				final Literal status = atom.mDecideStatus;
				if (status != lit.negate()) {
					/* check if clause is too old to keep */
					if (clause.mActivity < mClsScale * Config.CLAUSE_UNLEARN_ACTIVITY && status == null
							&& clause.doCleanup(this)) {
						clause.removeFromList();
					} else {
						/* watch this literal */
						for (int j = i; j > 2; j--) {
							lits[j] = lits[j - 1];
						}
						lits[2] = lits[index];
						lits[index] = lit;
						lit.mWatchers.append(clause, index);
					}
					continue nextList;
				}
			}
			/*
			 * Now we haven't found another atom to watch. Hence we have a unit clause or
			 * conflict clause.
			 *
			 * Note that we propagate otherAtom.
			 */
			if (otherAtom.mDecideStatus == null) {
				/*
				 * Put it on backtrack watchers of the other atom so it is reconsidered when we
				 * backtrack.
				 */
				otherAtom.mBacktrackWatchers.append(clause, index);
				/* Propagate the unit clause. */
				otherAtom.mExplanation = clause;
				mProps++;
				clause = setLiteral(otherLit);
			} else {
				/*
				 * clause is a conflict clause. After resolving this, we need to re-check this
				 * clause.
				 */
				mPendingWatcherList.append(clause, index);
			}
			/* Conflict clause */
			if (Config.PROFILE_TIME) {
				mPropClauseTime += System.nanoTime() - time - mSetTime;
			}
			return clause;// NOPMD
		}
		if (Config.PROFILE_TIME) {
			mPropClauseTime += System.nanoTime() - time - mSetTime;
		}
		return null;
	}

	private boolean checkConflict(final Clause conflict) {
		for (final Literal lit : conflict.mLiterals) {
			final DPLLAtom a = lit.getAtom();
			assert a.mDecideStatus == lit.negate();
		}
		return true;
	}

	/**
	 * Sets a literal to true and tells all theories about it. The literal must be
	 * undecided when this function is called.
	 *
	 * @param literal the literal to set.
	 * @return a conflict clause if a conflict was detected.
	 */
	@SuppressWarnings("unused")
	public Clause setLiteral(final Literal literal) {
		mLogger.debug("S %s", literal);
		final DPLLAtom atom = literal.getAtom();
		assert atom.mDecideStatus == null;
		assert mAtoms.contains(atom);
		atom.mStackPosition = mDPLLStack.size();
		mDPLLStack.add(literal);
		atom.mDecideLevel = mCurrentDecideLevel;
		atom.mDecideStatus = literal;
		if (!atom.preferredStatusIsLocked()) {
			atom.mLastStatus = atom.mDecideStatus;
		}
		mAtoms.remove(atom);
		assert !Config.EXPENSIVE_ASSERTS || checkDecideLevel();
		mPendingWatcherList.moveAll(literal.negate().mWatchers);
		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		Clause conflict = null;
		if (mCurrentDecideLevel <= mBaseLevel) {
			/* This atom is now decided once and for all. */
			mNumSolvedAtoms++;
			generateLevel0Proof(literal);
		}
		for (final ITheory t : mTheories) {
			conflict = t.setLiteral(literal);
			if (conflict != null) {
				assert checkConflict(conflict);
				break;
			}
		}
		if (Config.PROFILE_TIME) {
			mSetTime += System.nanoTime() - time;
		}
		return conflict;
	}

	public void watchClause(final Clause clause) {
		if (clause.getSize() <= 1) {
			if (clause.getSize() == 0) {
				if (mUnsatClause == null) {
					mUnsatClause = clause;
				}
			} else {
				/* propagate unit clause: only register watcher on "virtual" second literal. */
				mPendingWatcherList.append(clause, 1);
			}
		} else {
			/*
			 * A clause is "watched" if it appears on either the watcherBack/SetList or the
			 * watchers list of some atom.
			 */
			mPendingWatcherList.append(clause, 0);
			mPendingWatcherList.append(clause, 1);
		}
	}

	public void addClause(final Clause clause) {
		mAtomScale += 1.0 - 1.0 / Config.ATOM_ACTIVITY_FACTOR;
		clause.mActivity = Double.POSITIVE_INFINITY;
		mNumAxiomClauses++;
		assert clause.mStacklevel == mPushPopLevel;
		mClauses.prepend(clause);
		watchClause(clause);
	}

	void removeClause(final Clause c) {
		c.removeFromList();
	}

	public void addFormulaClause(final Literal[] literals, final ProofNode proof) {
		addFormulaClause(literals, proof, null);
	}

	public void addFormulaClause(final Literal[] literals, final ProofNode proof, final ClauseDeletionHook hook) {
		final Clause clause = new Clause(literals, mPushPopLevel);
		clause.setDeletionHook(hook);
		addClause(clause);
		if (isProofGenerationEnabled()) {
			assert proof instanceof LeafNode;
			clause.setProof(proof);
		}
		mLogger.trace("Added clause %s", clause);
	}

	public void learnClause(final Clause clause) {
		mAtomScale += 1.0 - 1.0 / Config.ATOM_ACTIVITY_FACTOR;
		mNumClauses++;
		clause.mActivity = mClsScale;// Double.POSITIVE_INFINITY;
		if (clause.getSize() <= 2) {
			clause.mActivity = Double.POSITIVE_INFINITY;
		}
		mLearnedClauses.append(clause);
		watchClause(clause);
	}

	// public void addInstantiationClause(Literal[] lits) {
	// ++num_insts;
	// Clause clause = new Clause(lits);
	// addClause(clause);
	// if (isProofGenerationEnabled()) {
	// // FIXME: This should somehow be related to the instantiation
	// LeafNode ln = new LeafNode(LeafNode.QUANT_INST, null, false);
	// clause.setProof(ln);
	// }
	// }

	private boolean checkDecideLevel() {
		int decision = 0;
		int i = 0;
		for (final Literal lit : mDPLLStack) {
			if (lit.getAtom().mExplanation == null) {
				decision++;
			}
			assert lit.getAtom().mStackPosition == i;
			assert lit.getAtom().mDecideLevel == decision;
			i++;
		}
		return decision == mCurrentDecideLevel;
	}

	private int countLitsOnDecideLevel(final Set<Literal> conflict) {
		int numLits = 0;
		int stackPtr = mDPLLStack.size();
		while (true) {
			final Literal lit = mDPLLStack.get(--stackPtr);
			assert !conflict.contains(lit.negate());
			if (conflict.contains(lit)) {
				numLits++;
			}
			if (lit.getAtom().mExplanation == null) {
				return numLits;
			}
		}
	}

	/**
	 * Explain one conflict clause. DO NOT CALL THIS FUNCTION DIRECTLY!!! USE
	 * {@link #explain(Clause)} INSTEAD SINCE THIS FUNCTION DOES A CORRECT LOOP
	 * INCLUDING {@link #finalizeBacktrack()} AND HENCE DOES NOT LEAVE BEHIND
	 * INCONSISTENT THEORY SOLVERS.
	 *
	 * @param clause Conflict clause
	 * @return Explanation
	 */
	private Clause explainConflict(final Clause clause) {
		mLogger.debug("explain conflict %s", clause);
		final HashSet<Literal> level0Ants = new HashSet<>();
		List<Antecedent> antecedents = null;
		if (isProofGenerationEnabled()) {
			antecedents = new ArrayList<>();
		}
		int expstacklevel = clause.mStacklevel;
		mConflicts++;
		assert checkDecideLevel();
		mAtomScale *= Config.ATOM_ACTIVITY_FACTOR;
		mClsScale *= Config.CLS_ACTIVITY_FACTOR;
		final Set<Literal> conflict = new CuckooHashSet<>();
		int maxDecideLevel = mBaseLevel + 1;
		int numLitsOnMaxDecideLevel = 0;
		int numAssumptions = 0;
		for (final Literal lit : clause.mLiterals) {
			final DPLLAtom atom = lit.getAtom();
			assert atom.mDecideStatus == lit.negate();
			if (atom.mDecideLevel > mBaseLevel) {
				if (atom.mDecideLevel >= maxDecideLevel) {
					if (atom.mDecideLevel > maxDecideLevel) {
						maxDecideLevel = atom.mDecideLevel;
						numLitsOnMaxDecideLevel = 1;
					} else {
						numLitsOnMaxDecideLevel++;
					}
				}
				conflict.add(lit.negate());
			} else {
				if (mAssumptionLiterals.contains(lit.negate())) {
					conflict.add(lit.negate());
					++numAssumptions;
				} else {
					expstacklevel = level0resolve(lit, level0Ants, expstacklevel);
				}
			}
			atom.mActivity += mAtomScale;
		}
		mLogger.debug("removing level0: %s", conflict);
		if (conflict.size() == numAssumptions) {
			/*
			 * Unsatisfiable
			 */
			/* add assumptions from level0 antecedents */
			for (final Literal lit0 : level0Ants) {
				final Clause c = getLevel0(lit0);
				for (final Literal assumptionLit : c.mLiterals) {
					if (assumptionLit != lit0) {
						conflict.add(assumptionLit.negate());
					}
				}
			}
			final Literal[] newlits = new Literal[conflict.size()];
			int i = 0;
			for (final Literal l : conflict) {
				newlits[i++] = l.negate();
			}
			assert i == newlits.length;
			final Clause resolution = new Clause(newlits, expstacklevel);
			if (isProofGenerationEnabled()) {
				for (final Literal l0 : level0Ants) {
					antecedents.add(new Antecedent(l0, getLevel0(l0)));
				}
				if (antecedents.isEmpty()) {
					// TODO: only one clause object needed here.
					resolution.setProof(clause.getProof());
				} else {
					final Antecedent[] ants = antecedents.toArray(new Antecedent[antecedents.size()]);
					resolution.setProof(new ResolutionNode(clause, ants));
				}
			}
			// Remember unsat clause (which might not be empty, by conflicting
			// against assumptions)
			mUnsatClause = resolution;
			return resolution;
		}
		assert numLitsOnMaxDecideLevel >= 1;
		while (mCurrentDecideLevel > maxDecideLevel) {
			final Literal lit = mDPLLStack.remove(mDPLLStack.size() - 1);
			assert !conflict.contains(lit.negate());
			assert !conflict.contains(lit);
			backtrackLiteral(lit);
			assert checkDecideLevel();
		}
		while (numLitsOnMaxDecideLevel > 1) {
			assert checkDecideLevel();
			assert mCurrentDecideLevel == maxDecideLevel;
			assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
			assert checkDecideLevel();
			final Literal lit = mDPLLStack.get(mDPLLStack.size() - 1);
			assert !conflict.contains(lit.negate());
			if (!conflict.contains(lit)) {
				assert lit.getAtom().mExplanation != null;
				assert checkDecideLevel();
				mDPLLStack.remove(mDPLLStack.size() - 1);
				backtrackLiteral(lit);
				assert checkDecideLevel();
				continue;
			}

			/* Do a resolution step with explanation */
			final Clause expl = getExplanation(lit);
			expl.mActivity += mClsScale;
			// expl.usedTimes++;
			expstacklevel = Math.max(expstacklevel, expl.mStacklevel);
			if (isProofGenerationEnabled()) {
				antecedents.add(new Antecedent(lit, expl));
			}
			mDPLLStack.remove(mDPLLStack.size() - 1);
			backtrackLiteral(lit);
			assert checkDecideLevel();
			conflict.remove(lit);
			numLitsOnMaxDecideLevel--;
			final DPLLAtom atom = lit.getAtom();
			mLogger.debug("Resolving with %s pivot = %s", expl, atom);
			for (final Literal l : expl.mLiterals) {
				if (l != lit) {
					assert l.getAtom().mDecideStatus == l.negate();
					final int level = l.getAtom().mDecideLevel;
					if (mAssumptionLiterals.contains(l.negate())) {
						if (conflict.add(l.negate())) {
							++numAssumptions;
						}
					} else if (level > mBaseLevel) {
						if (conflict.add(l.negate()) && level == maxDecideLevel) {
							numLitsOnMaxDecideLevel++;
						}
					} else {
						// Here, we do level0 resolution as well
						expstacklevel = level0resolve(l, level0Ants, expstacklevel);
					}
					l.getAtom().mActivity += mAtomScale;
				}
			}
			assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
			mLogger.debug("new conflict: %s", conflict);
		}
		assert mCurrentDecideLevel == maxDecideLevel;
		assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
		assert numLitsOnMaxDecideLevel == 1;
		while (mCurrentDecideLevel >= maxDecideLevel) {
			final Literal lit = mDPLLStack.remove(mDPLLStack.size() - 1);
			assert !conflict.contains(lit.negate());
			backtrackLiteral(lit);
			assert checkDecideLevel();
		}
		/*
		 * We removed at least one decision point. Try to backtrack further.
		 */
		if (Config.DEEP_BACKTRACK) {
			findBacktrackingPoint(conflict);
		}

		mLogger.debug("Backtrack to %d", mDPLLStack.size());

		final HashMap<Literal, Integer> redundancy = computeRedundancy(conflict);
		final Integer REDUNDANT = 1;

		int stackPtr = mDPLLStack.size();
		while (stackPtr > mNumSolvedAtoms) {
			final Literal lit = mDPLLStack.get(--stackPtr);
			if (redundancy.get(lit) == REDUNDANT && conflict.contains(lit)) {
				/* Do a resolution step with explanation */
				final Clause expl = getExplanation(lit);
				expl.mActivity += mClsScale;
				// expl.usedTimes++;
				expstacklevel = Math.max(expstacklevel, expl.mStacklevel);
				if (isProofGenerationEnabled()) {
					antecedents.add(new Antecedent(lit, expl));
				}
				conflict.remove(lit);
				for (final Literal l : expl.mLiterals) {
					if (l != lit) {
						assert l.getAtom().mDecideStatus == l.negate();
						final int level = l.getAtom().mDecideLevel;
						if (mAssumptionLiterals.contains(l.negate())) {
							if (conflict.add(l.negate())) {
								++numAssumptions;
							}
						} else if (level > mBaseLevel) {
							conflict.add(l.negate());
						} else {
							// Here, we do level0 resolution as well
							expstacklevel = level0resolve(l, level0Ants, expstacklevel);
						}
						l.getAtom().mActivity += mAtomScale;
					}
				}
			}
		}
		mLogger.debug("removing redundancy yields %s", conflict);
		/* add assumptions from level0 antecedents */
		for (final Literal lit0 : level0Ants) {
			final Clause c = getLevel0(lit0);
			for (final Literal assumptionLit : c.mLiterals) {
				if (assumptionLit != lit0) {
					conflict.add(assumptionLit.negate());
				}
			}
		}
		final Literal[] newlits = new Literal[conflict.size()];
		int i = 0;
		for (final Literal l : conflict) {
			newlits[i++] = l.negate();
		}
		assert newlits[newlits.length - 1] != null;
		final Clause resolution = new Clause(newlits, expstacklevel);
		if (isProofGenerationEnabled()) {
			for (final Literal l0 : level0Ants) {
				antecedents.add(new Antecedent(l0, getLevel0(l0)));
			}
			if (antecedents.isEmpty()) {
				// TODO: only one clause object needed here.
				resolution.setProof(clause.getProof());
			} else {
				final Antecedent[] ants = antecedents.toArray(new Antecedent[antecedents.size()]);
				resolution.setProof(new ResolutionNode(clause, ants));
			}
		}
		mLogger.debug("Resolved to %s", resolution);
		// If resolution size is number of literals we are unsat
		if (newlits.length == numAssumptions) {
			mUnsatClause = resolution;
		}
		return resolution;
	}

	/**
	 * Explain all conflicts currently present in the solver starting with a given
	 * initial conflict. Returns <code>true</code> if and only if the empty clause
	 * has been derived.
	 *
	 * @param conflict The initial conflict.
	 * @return Is the solver inconsistent?
	 */
	private boolean explain(Clause conflict) {
		while (conflict != null) {
			startBacktrack();
			conflict = explainConflict(conflict);
			learnClause(conflict);
			if (mUnsatClause != null) {
				return true;
			}
			conflict = finalizeBacktrack();
		}
		return false;
	}

	private final int level0resolve(final Literal l, final Set<Literal> level0Ants, final int sl) {
		final Clause l0 = getLevel0(l.negate());
		level0Ants.add(l.negate());
		return l0.mStacklevel > sl ? l0.mStacklevel : sl;
	}

	private Clause getExplanation(final Literal lit) {
		final Object explanation = lit.getAtom().mExplanation;
		if (explanation instanceof ITheory) {
			final Clause expl = ((ITheory) explanation).getUnitClause(lit);
			lit.getAtom().mExplanation = expl;
			assert checkUnitClause(expl, lit);
			assert checkDecideLevel();
			return expl;
		} else {
			assert explanation == null || checkUnitClause((Clause) explanation, lit);
			return (Clause) explanation;
		}
	}

	private HashMap<Literal, Integer> computeRedundancy(final Set<Literal> conflict) {
		final Integer REDUNDANT = 1;
		final Integer FAILED = 2;
		final Integer KEEP = 3;// NOCHECKSTYLE
		final HashMap<Literal, Integer> status = new HashMap<>();
		for (final Literal l : conflict) {
			if (l.getAtom().getDecideStatus() != null) {
				assert l.getAtom().getDecideStatus() == l;
				status.put(l, REDUNDANT);
			}
		}
		final ArrayDeque<Literal> todo = new ArrayDeque<>();
		final Iterator<Literal> it = conflict.iterator();
		litloop: while (it.hasNext()) {
			final Literal lit = it.next();
			if (lit.getAtom().getDecideStatus() == null) {
				continue;
			}
			todo.addFirst(lit);
			todoloop: while (!todo.isEmpty()) {
				final Literal next = todo.getFirst();
				assert next.getAtom().getDecideStatus() == next;
				final Clause expl = getExplanation(next);
				// logger.info("check "+next+" expl "+expl);
				if (expl == null) {
					while (todo.size() > 1) {
						status.put(todo.removeFirst(), FAILED);
					}
					status.put(todo.removeFirst(), KEEP);
					continue litloop;
				}
				for (final Literal l : expl.mLiterals) {
					assert l.getAtom().getDecideStatus() != null;
					if (l != next && l.getAtom().getDecideLevel() > mBaseLevel) {
						final Literal lneg = l.negate();
						assert lneg.getAtom().getDecideStatus() == lneg;
						final Integer st = status.get(lneg);
						if (st == FAILED) {
							while (todo.size() > 1) {
								status.put(todo.removeFirst(), FAILED);
							}
							status.put(todo.removeFirst(), KEEP);
							continue litloop;
						} else if (st == null) {
							todo.addFirst(lneg);
							continue todoloop;
						}
					}
				}
				status.put(todo.removeFirst(), REDUNDANT);
			}
		}
		return status;
	}

	private boolean checkUnitClause(final Clause unit, final Literal lit) {
		boolean found = false;
		for (final Literal l : unit.mLiterals) {
			assert l != lit.negate() : "Negation of unit literal in explanation";
			if (l == lit) {
				found = true;
			} else {
				assert l.mAtom.mDecideStatus == l.negate()
						&& l.mAtom.getStackPosition() < lit.getAtom().getStackPosition() : // NOCHECKSTYLE
				"Not a unit clause: " + l + " in " + unit;
			}
		}
		assert found : "Unit literal not in explanation";
		return found;
	}

	private void startBacktrack() {
		for (final ITheory t : mTheories) {
			t.backtrackStart();
		}
	}

	private Clause finalizeBacktrack() {
		for (final ITheory t : mTheories) {
			final Clause conflict = t.backtrackComplete();
			if (conflict != null) {
				return conflict;
			}
		}
		return null;
	}

	private void findBacktrackingPoint(final Set<Literal> conflict) {
		int i = mDPLLStack.size();
		while (i > 0) {
			final Literal lit = mDPLLStack.get(--i);
			if (conflict.contains(lit)) {
				break;
			}
			if (lit.getAtom().mExplanation == null) {
				while (mDPLLStack.size() > i) {
					backtrackLiteral(mDPLLStack.remove(mDPLLStack.size() - 1));
				}
			}
		}
	}

	public void backtrackLiteral(final Literal literal) {
		long time;
		mLogger.debug("B %s", literal);
		final DPLLAtom atom = literal.getAtom();
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		for (final ITheory t2 : mTheories) {
			t2.backtrackLiteral(literal);
		}
		if (Config.PROFILE_TIME) {
			mBacktrackTime += System.nanoTime() - time;
		}
		mPendingWatcherList.moveAll(atom.mBacktrackWatchers);
		if (atom.mExplanation == null) {
			decreaseDecideLevel();
		}
		atom.mExplanation = null;
		atom.mDecideStatus = null;
		atom.mDecideLevel = -1;
		atom.mStackPosition = -1;
		mAtoms.add(atom);
	}

	private Clause checkConsistency() {
		long time = 0;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		mLogger.debug("DPLL: final check");
		for (final ITheory t : mTheories) {
			final Clause conflict = t.computeConflictClause();
			if (conflict != null) {
				return conflict;
			}
			if (!mAtoms.isEmpty()) {
				break;
			}
		}
		if (Config.PROFILE_TIME) {
			mCheckTime += System.nanoTime() - time;
		}
		return null;
	}

	private Literal chooseLiteral() {
		final Literal lit = suggestions();
		if (lit != null) {
			return lit;
		}
		DPLLAtom atom;
		// int ran = mRandom.nextInt(Config.RANDOM_SPLIT_BASE);
		// if (!mAtoms.isEmpty() && ran <= Config.RANDOM_SPLIT_FREQ) {
		// atom = mAtoms.mAtoms[mRandom.nextInt(mAtoms.size())];
		// ++mNumRandomSplits;
		// } else
		atom = mAtoms.peek();
		if (atom == null) {
			return null;
		}
		assert atom.mDecideStatus == null;
		// logger.debug("Choose literal: "+atom+" Weight "
		// + (atom.activity/factor) +" - last: " + atom.lastStatus);
		// return atom.lastStatus == null ? atom.negate() : atom.lastStatus;
		return atom.getPreferredStatus();
	}

	private static final int luby_super(final int i) {
		int power;

		assert i > 0;
		/* let 2^k be the least power of 2 >= (i+1) */
		power = 2;
		while (power < i + 1) {
			power *= 2;
		}
		if (power == i + 1) {
			return power / 2;
		}
		return luby_super(i - power / 2 + 1);
	}

	private void printStatistics() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Confl: " + mConflicts + " Props: " + mProps + " Tprops: " + mTProps + " Decides: " + mDecides
					+ " RSplits: " + mNumRandomSplits);
			if (Config.PROFILE_TIME) {
				mLogger.info("Times: Expl: " + mExplainTime / 1000 / 1000.0// NOCHECKSTYLE
						+ " Prop: " + mPropTime / 1000 / 1000.0// NOCHECKSTYLE
						+ " PropClause: " + mPropClauseTime / 1000 / 1000.0// NOCHECKSTYLE
						+ " Set: " + mSetTime / 1000 / 1000.0// NOCHECKSTYLE
						+ " Check: " + mCheckTime / 1000 / 1000.0// NOCHECKSTYLE
						+ " Back: " + mBacktrackTime / 1000 / 1000.0);// NOCHECKSTYLE
			}
			mLogger.info("Atoms: " + mNumSolvedAtoms + "/" + (mAtoms.size() + mDPLLStack.size()) + " Clauses: "
					+ mNumClauses + " Axioms: " + mNumAxiomClauses);
			for (final ITheory t : mTheories) {
				t.printStatistics(mLogger);
			}
		}
	}

	/**
	 * Solves the current problem.
	 *
	 * @return true if sat, false if unsat.
	 */
	public boolean solve() {
		mHasModel = false;
		if (mUnsatClause != null) {
			mLogger.debug("Using cached unsatisfiability");
			return false;
		}
		try {
			if (Config.INITIAL_PHASE_BIAS_JW) {
				// Compute for all remaining atoms an initial polarity according
				// to Jeruslaw Wang
				final Map<Literal, Double> scores = new HashMap<>();
				clause_loop: for (final Clause c : mClauses) {
					double inc = 1.0;
					for (final Literal lit : c.mLiterals) {
						final Literal ds = lit.getAtom().getDecideStatus();
						if (ds == lit) {
							// clause is satisfied
							continue clause_loop;
						}
						if (ds != lit.negate()) {
							inc /= 2.0;
						}
					}
					// Here, clause is not satisfied
					for (final Literal lit : c.mLiterals) {
						final Literal ds = lit.getAtom().getDecideStatus();
						if (ds != lit.negate()) {
							final Double score = scores.get(lit);
							if (score == null) {
								scores.put(lit, inc);
							} else {
								scores.put(lit, score + inc);
							}
						}
					}
				}
				for (final DPLLAtom atom : mAtoms) {
					final Double pscore = scores.get(atom);
					final Double nscore = scores.get(atom.negate());
					final double Pscore = pscore == null ? 0 : pscore;
					final double Nscore = nscore == null ? 0 : nscore;
					if (!atom.preferredStatusIsLocked()) {
						atom.setPreferredStatus(Pscore > Nscore ? atom : atom.negate());
					}
				}
			}
			long lastTime;
			if (Config.PROFILE_TIME) {
				lastTime = System.nanoTime() - mSetTime - mBacktrackTime;
			}
			for (final ITheory t : mTheories) {
				final Clause conflict = t.startCheck();
				if (explain(conflict)) {
					return false;
				}
			}
			int iteration = 1;
			int nextRestart = Config.RESTART_FACTOR;
			long time;
			while (!isTerminationRequested()) {
				Clause conflict;
				do {
					conflict = propagateInternal();
					if (conflict != null || isTerminationRequested()) {
						break;
					}
					if (Config.PROFILE_TIME) {
						time = System.nanoTime();
						mPropTime += time - lastTime - mSetTime - mBacktrackTime;
						lastTime = time - mSetTime - mBacktrackTime;
					}
					final Literal literal = chooseLiteral();
					if (literal == null) {
						conflict = checkConsistency();
						if (conflict == null) {
							Literal lit;
							boolean suggested = false;
							while (conflict != null && (lit = suggestions()) != null) { // NOPMD
								if (lit.getAtom().mExplanation == null) {
									increaseDecideLevel();
									mDecides++;
								}
								conflict = setLiteral(lit);
								suggested = true;
							}
							// @assert conflict != null ==> suggested == true
							if (!suggested && mPendingWatcherList.isEmpty() && mAtoms.isEmpty()) {
								/* We found a model */
								if (mLogger.isInfoEnabled()) {
									printStatistics();
									mLogger.info("Hooray, we found a model:");
									for (final ITheory t : mTheories) {
										t.dumpModel(mLogger);
									}
									if (mLogger.isTraceEnabled()) {
										for (final Literal dlit : mDPLLStack) {
											mLogger.trace("%d: %s", dlit.hashCode(), dlit);
										}
									}
								}
								mHasModel = true;
								return true;
							}
						}
					} else {
						increaseDecideLevel();
						mDecides++;
						conflict = setLiteral(literal);
					}
				} while (conflict == null && !isTerminationRequested());
				if (Config.PROFILE_TIME) {
					time = System.nanoTime();
					mPropTime += time - lastTime - mSetTime - mBacktrackTime;
					lastTime = time - mSetTime - mBacktrackTime;
				}
				if (explain(conflict)) {
					if (Config.PROFILE_TIME) {
						time = System.nanoTime();
						mExplainTime += time - lastTime - mSetTime - mBacktrackTime;
						lastTime = time - mSetTime - mBacktrackTime;
					}
					printStatistics();
					mLogger.info("Formula is unsat");
					/*
					 * logger.info("Learned Clauses"); for (Clause c : learnedClauses) {
					 * logger.info("Cl: len "+c.literals.length+ " used "+c.usedTimes + ": "+c); }
					 */
					return false;
				}
				if (Config.PROFILE_TIME) {
					time = System.nanoTime();
					mExplainTime += time - lastTime - mSetTime - mBacktrackTime;
					lastTime = time - mSetTime - mBacktrackTime;
				}
				if (mAtomScale > Config.LIMIT) {
					for (final DPLLAtom a : mAtoms) {
						a.mActivity *= Double.MIN_NORMAL;
					}
					for (final Literal l : mDPLLStack) {
						l.getAtom().mActivity *= Double.MIN_NORMAL;
					}
					mAtomScale *= Double.MIN_NORMAL;
				}
				if (mClsScale > Config.LIMIT) {
					final Iterator<Clause> it = mLearnedClauses.iterator();
					while (it.hasNext()) {
						final Clause c = it.next();
						c.mActivity *= Double.MIN_NORMAL;
					}
					mClsScale *= Double.MIN_NORMAL;
				}
				if (--nextRestart == 0) {
					startBacktrack();
					final DPLLAtom next = mAtoms.peek();
					int restartpos = -1;
					for (int i = mNumSolvedAtoms + mBaseLevel; i < mDPLLStack.size(); ++i) {
						final DPLLAtom var = mDPLLStack.get(i).getAtom();
						if (var.mExplanation == null && var.mActivity < next.mActivity) {
							// This has been a decision
							restartpos = i;
							break;
						}
					}
					if (restartpos != -1) {
						while (mDPLLStack.size() > restartpos) {
							final Literal lit = mDPLLStack.remove(mDPLLStack.size() - 1);
							assert lit.getAtom().mDecideLevel != mBaseLevel;
							final Object litexpl = lit.getAtom().mExplanation;
							if (litexpl instanceof Clause) {
								((Clause) litexpl).mActivity += mClsScale;
								// ((Clause) litexpl).usedTimes++;
							}
							backtrackLiteral(lit);
						}
					}
					unlearnClauses(mPushPopLevel);
					conflict = finalizeBacktrack();
					assert conflict == null;
					iteration++;
					for (final ITheory t : mTheories) {
						t.restart(iteration);
					}
					nextRestart = Config.RESTART_FACTOR * luby_super(iteration);
					if (Config.PRINT_STATISTICS) {
						mLogger.info("Restart");
						printStatistics();
					}
				}
				if (Config.PROFILE_TIME) {
					lastTime = System.nanoTime() - mSetTime - mBacktrackTime;
				}
			}
			return true;
		} catch (final OutOfMemoryError eOOM) {
			setCompleteness(INCOMPLETE_MEMOUT);
			return true;
		} finally {
			for (final ITheory t : mTheories) {
				t.endCheck();
			}
		}
	}

	private final void unlearnClauses(final int targetstacklevel) {
		final Iterator<Clause> it = mLearnedClauses.iterator();
		while (it.hasNext()) {
			final Clause c = it.next();
			if (c.mActivity < mClsScale * Config.CLAUSE_UNLEARN_ACTIVITY
					|| c.mStacklevel > targetstacklevel && c.doCleanup(this)) {
				mNumClauses--;
				it.remove();
			}
		}
	}

	private Literal suggestions() {
		for (final ITheory t : mTheories) {
			final Literal lit = t.getPropagatedLiteral();
			if (lit != null) {
				lit.mAtom.mExplanation = t;
				assert lit.getAtom().mDecideStatus == null;
				return lit;
			}
		}
		for (final ITheory t : mTheories) {
			final Literal lit = t.getSuggestion();
			if (lit != null) {
				assert lit.getAtom().mDecideStatus == null;
				return lit;
			}
		}
		return null;
	}

	public void addAtom(final DPLLAtom atom) {
		mAtoms.add(atom);
		mAtomList.add(atom);
	}

	public void removeAtom(final DPLLAtom atom) {
		assert atom.mDecideStatus == null;
		mAtoms.remove(atom);
		for (final ITheory t : mTheories) {
			t.removeAtom(atom);
		}
	}

	public void addTheory(final ITheory t) {
		final ITheory[] newTheories = new ITheory[mTheories.length + 1];
		System.arraycopy(mTheories, 0, newTheories, 0, mTheories.length);
		newTheories[mTheories.length] = t;
		mTheories = newTheories;
	}

	public void removeTheory() {
		final ITheory[] newTheories = new ITheory[mTheories.length - 1];
		System.arraycopy(mTheories, 0, newTheories, 0, mTheories.length);
		mTheories = newTheories;
	}

	public String dumpClauses(final Theory smtTheory) {
		final StringBuilder sb = new StringBuilder();
		for (final Clause c : mClauses) {
			sb.append("(assert ");
			final Literal[] lits = c.mLiterals;
			if (lits.length == 1) {
				sb.append(lits[0].getSMTFormula(smtTheory)).append(")\n");
			} else {
				sb.append("(or");
				for (final Literal l : lits) {
					sb.append(' ').append(l.getSMTFormula(smtTheory));
				}
				sb.append("))\n");
			}
		}
		return sb.toString();
	}

	public void setCompleteness(final int ncompleteness) {
		mCompleteness = ncompleteness;
	}

	public int getCompleteness() {
		return mCompleteness;
	}

	public void provideCompleteness(final int ncompleteness) {
		if (mCompleteness == COMPLETE) {
			mCompleteness = ncompleteness;
		}
	}

	public String getCompletenessReason() {
		return COMPLETENESS_STRINGS[mCompleteness];
	}

	public void push() {
		if (mAssignments != null) {
			mAssignments.beginScope();
		}
		mAtomList.beginScope();
		for (final ITheory theory : getAttachedTheories()) {
			theory.push();
		}
		++mPushPopLevel;
	}

	public void pop(final int numpops) {
		if (numpops < 1 || numpops > mPushPopLevel) {
			throw new IllegalArgumentException("Must pop a positive number less than the current stack level");
		}
		final int targetstacklevel = mPushPopLevel - numpops;
		if (mUnsatClause != null && mUnsatClause.mStacklevel > targetstacklevel) {
			mUnsatClause = null;
		}
		if (Config.EXPENSIVE_ASSERTS && !checkProofStackLevel(mUnsatClause, targetstacklevel)) {
			throw new AssertionError();
		}
		if (!mDPLLStack.isEmpty()) {
			final java.util.ListIterator<Literal> literals = mDPLLStack.listIterator(mDPLLStack.size());
			while (literals.hasPrevious()) {
				final Literal lit = literals.previous();
				final Object litexpl = lit.getAtom().mExplanation;
				if (litexpl instanceof Clause) {
					((Clause) litexpl).mActivity += mClsScale;
					// ((Clause) litexpl).usedTimes++;
				}
				backtrackLiteral(lit);
			}
			mDPLLStack.clear();
			for (final ITheory t : mTheories) {
				t.backtrackAll();
			}
		}
		unlearnClauses(targetstacklevel);
		assert mCurrentDecideLevel == 0;
		mNumSolvedAtoms = 0;
		final Iterator<Clause> inputit = mClauses.iterator();
		while (inputit.hasNext()) {
			final Clause input = inputit.next();
			if (input.mStacklevel > targetstacklevel) {
				if (input.doCleanup(this)) {
					inputit.remove();
				} else {
					throw new InternalError("Input clause still blocked, but invalid");
					// mLogger.debug("Removed clause %s", input);
				}
			} else {
				// Terminate iteration here since only clauses with lower
				// stacklevel remain.
				// mLogger.debug("Keeping input %s", input);
				break;
			}
		}
		for (int i = 0; i < numpops; ++i) {
			for (final ITheory theory : getAttachedTheories()) {
				theory.pop();
			}
			if (mAssignments != null) {
				mAssignments.endScope();
			}
			for (final DPLLAtom atom : mAtomList.currentScope()) {
				removeAtom(atom);
			}
			mAtomList.endScope();
			mPushPopLevel--;
		}
		mCompleteness = COMPLETE;
		assert mPushPopLevel == targetstacklevel;
	}

	public LogProxy getLogger() {
		return mLogger;
	}

	public void showClauses(final PrintWriter pw) {
		SimpleListable<Clause> c = mClauses.mNext;
		while (c != mClauses) {
			pw.println(c);
			c = c.mNext;
		}
	}

	public boolean hasModel() {
		for (final ITheory t : mTheories) {
			provideCompleteness(t.checkCompleteness());
		}
		return mHasModel && mCompleteness == COMPLETE;
	}

	public void setProofGeneration(final boolean enablePG) {
		mPGenabled = enablePG;
	}

	public boolean isProofGenerationEnabled() {
		return mPGenabled;
	}

	public Literal[] getUnsatAssumptions() {
		return mUnsatClause.mLiterals;
	}

	public Clause getProof() {
		assert checkValidUnsatClause();
		Clause empty = mUnsatClause;
		if (mUnsatClause != null && mUnsatClause.getSize() > 0) {
			// We have to remove the assumptions via resolution
			final Antecedent[] antecedents = new Antecedent[mUnsatClause.getSize()];
			for (int i = 0; i < mUnsatClause.getSize(); ++i) {
				final Literal lit = mUnsatClause.getLiteral(i).negate();
				antecedents[i] = new Antecedent(lit,
						new Clause(new Literal[] { lit }, new LeafNode(LeafNode.ASSUMPTION, null)));
			}
			final ResolutionNode proof = new ResolutionNode(mUnsatClause, antecedents);
			empty = new Clause(new Literal[0], proof);
		}
		return empty;
	}

	private void generateLevel0Proof(final Literal lit) {
		assert lit.getAtom().mDecideLevel <= mBaseLevel : "Level0 proof for non-level0 literal?";
		assert !mAssumptionLiterals.contains(lit);
		final HashSet<Literal> clauseLits = new HashSet<>();
		final Clause c = getExplanation(lit);
		if (c.getSize() > 1) {
			int stacklvl = c.mStacklevel;
			final Literal[] lits = c.mLiterals;
			Clause res;
			final Antecedent[] ants = isProofGenerationEnabled() ? new Antecedent[c.getSize() - 1] : null;
			int i = 0;
			for (final Literal l : lits) {
				if (mAssumptionLiterals.contains(l.negate())) {
					clauseLits.add(l);
				} else if (l != lit) {
					final Clause lc = getLevel0(l.negate());
					if (isProofGenerationEnabled()) {
						ants[i++] = new Antecedent(l.negate(), lc);
					}
					for (int j = 0; j < lc.getSize(); j++) {
						final Literal depLit = lc.getLiteral(j);
						if (depLit != l.negate()) {
							assert mAssumptionLiterals.contains(depLit.negate());
							clauseLits.add(depLit);
						}
					}
					stacklvl = Math.max(stacklvl, lc.mStacklevel);
				}
			}
			clauseLits.add(lit);
			final Literal[] arrayLits = clauseLits.toArray(new Literal[clauseLits.size()]);
			if (isProofGenerationEnabled()) {
				res = new Clause(arrayLits, new ResolutionNode(c, ants), stacklvl);
			} else {
				res = new Clause(arrayLits, stacklvl);
			}
			lit.getAtom().mExplanation = res;
		}
	}

	private boolean checkLevel0Clause(final Clause clause, final Literal lit) {
		boolean found = false;
		for (final Literal l : clause.mLiterals) {
			if (l == lit) {
				found = true;
			} else {
				assert mAssumptionLiterals.contains(l.negate());
			}
		}
		return found;
	}

	private Clause getLevel0(final Literal lit) {
		assert lit.getAtom().mDecideLevel <= mBaseLevel;
		final Object expl = lit.getAtom().mExplanation;
		assert expl instanceof Clause;
		assert checkLevel0Clause((Clause) expl, lit);
		return (Clause) expl;
	}

	public final void increaseDecideLevel() {
		mLogger.debug("Decide@%d", mDPLLStack.size());
		mCurrentDecideLevel++;
		assert mCurrentDecideLevel >= 0 : "Decidelevel negative";
		for (final ITheory t : mTheories) {
			t.increasedDecideLevel(mCurrentDecideLevel);
		}
	}

	public final void decreaseDecideLevel() {
		mCurrentDecideLevel--;
		assert mCurrentDecideLevel >= 0 : "Decidelevel negative";
		for (final ITheory t : mTheories) {
			t.decreasedDecideLevel(mCurrentDecideLevel);
		}
	}

	public ITheory[] getAttachedTheories() {
		return mTheories;
	}

	public int getAssertionStackLevel() {
		return mPushPopLevel;
	}

	public boolean inconsistent() {
		return mUnsatClause != null;
	}

	private boolean checkProofStackLevel(final Clause c, final int targetlvl) {
		if (c == null || c.mProof == null) {
			return true;
		}
		if (c.mStacklevel > targetlvl) {
			System.err.println("Clause " + c + " above target level!");
			return false;
		}
		for (final Literal lit : c.mLiterals) {
			if (lit.getAtom().mAssertionstacklevel > targetlvl) {
				System.err.println("Literal " + lit + " in clause " + c + " above target level");
				return false;
			}
		}
		if (c.mProof instanceof ResolutionNode) {
			final ResolutionNode rn = (ResolutionNode) c.mProof;
			if (!checkProofStackLevel(rn.getPrimary(), targetlvl)) {
				return false;
			}
			for (final Antecedent ante : rn.getAntecedents()) {
				if (!checkProofStackLevel(ante.mAntecedent, targetlvl)) {
					return false;
				}
			}
		}
		return true;
	}

	public Object getStatistics() {
		final Object[] res = new Object[mTheories.length + 1];
		final Object[] mystats = new Object[][] { { "Conflicts", mConflicts }, { "Propagations", mProps },
				{ "Theory_propagations", mTProps }, { "Decides", mDecides }, { "Random_splits", mNumRandomSplits },
				{ "Num_Atoms", mAtoms.size() + mDPLLStack.size() }, { "Solved_Atoms", mNumSolvedAtoms },
				{ "Clauses", mNumClauses }, { "Axioms", mNumAxiomClauses },
				{ "Times", new Object[][] { { "Explain", mExplainTime }, { "Propagation", mPropTime },
						{ "Set", mSetTime }, { "Check", mCheckTime }, { "Backtrack", mBacktrackTime } } } };
		res[0] = new Object[] { ":Core", mystats };
		for (int i = 1; i < res.length; ++i) {
			res[i] = mTheories[i - 1].getStatistics();
		}
		return res;
	}

	public void setProduceAssignments(final boolean value) {
		assert mPushPopLevel == 0 && mAssignments == null || mAssignments.isEmpty();
		if (value) {
			mAssignments = new ScopedHashMap<>();
		} else {
			mAssignments = null;
		}
	}

	public boolean isProduceAssignments() {
		return mAssignments != null;
	}

	public void trackAssignment(final String label, final Literal literal) {
		mAssignments.put(label, literal);
	}

	public Assignments getAssignments() {
		if (!isProduceAssignments()) {
			return null;
		}
		final HashMap<String, Boolean> assignment = new HashMap<>(mAssignments.size(), 1.0f);
		for (final Map.Entry<String, Literal> me : mAssignments.entrySet()) {
			assignment.put(me.getKey(), me.getValue().getAtom().mDecideStatus == me.getValue());
		}
		return new Assignments(assignment);
	}

	/**
	 * Run a quick and incomplete check on the current context. This only uses
	 * propagations and a conflict explanation to the empty clause.
	 *
	 * @return <code>false</code> if and only if the empty clause could be derived.
	 */
	public boolean quickCheck() {
		if (mUnsatClause != null) {
			return false;
		}
		final Clause conflict = propagateInternal();
		final boolean res = !explain(conflict);
		return res;
	}

	/**
	 * Propagate as much as possible. In contrast to {@link #quickCheck()}, this
	 * function tells the theory solvers to start a check. This might get more
	 * propagations than {@link #quickCheck()}.
	 *
	 * @return <code>false</code> if and only if the empty clause could be derived.
	 */
	public boolean propagate() {
		if (mUnsatClause != null) {
			return false;
		}
		Clause conflict = null;
		for (final ITheory t : mTheories) {
			conflict = t.startCheck();
			if (conflict != null) {
				break;
			}
		}
		if (conflict == null) {
			conflict = propagateInternal();
		}
		final boolean res = !explain(conflict);
		for (final ITheory t : mTheories) {
			t.endCheck();
		}
		return res;
	}

	public Random getRandom() {
		return mRandom;
	}

	public void setRandomSeed(final long seed) {
		mRandom.setSeed(seed);
	}

	public void flipDecisions() {
		startBacktrack();
		while (mDPLLStack.size() > mBaseLevel + mNumSolvedAtoms) {
			final Literal lit = mDPLLStack.remove(mDPLLStack.size() - 1);
			backtrackLiteral(lit);
			// Flip the decision
			lit.getAtom().mLastStatus = lit.negate();
		}
		final Clause conflict = finalizeBacktrack();
		assert conflict == null;
		assert mCurrentDecideLevel == mBaseLevel;
	}

	public void flipNamedLiteral(final String name) throws SMTLIBException {
		startBacktrack();
		while (mDPLLStack.size() > mBaseLevel + mNumSolvedAtoms) {
			final Literal lit = mDPLLStack.remove(mDPLLStack.size() - 1);
			backtrackLiteral(lit);
		}
		final Clause conflict = finalizeBacktrack();
		assert conflict == null;
		assert mCurrentDecideLevel == mBaseLevel;
		final Literal lit = mAssignments.get(name);
		if (lit == null) {
			throw new SMTLIBException("Name " + name + " not known");
		}
		final DPLLAtom atom = lit.getAtom();
		atom.mLastStatus = atom.mLastStatus == null ? atom : atom.mLastStatus.negate();
	}

	/**
	 * Returns the list of all input clauses. This list does not contain any learned
	 * clauses!
	 */
	public SimpleList<Clause> getClauses() {
		return mClauses;
	}

	public Term[] getSatisfiedLiterals(final Theory smtTheory) {
		int size = 0;
		for (final Literal lit : mDPLLStack) {
			if (!(lit.getAtom() instanceof NamedAtom)) {
				++size;
			}
		}
		final Term[] res = new Term[size];
		int i = -1;
		for (final Literal lit : mDPLLStack) {
			if (!(lit.getAtom() instanceof NamedAtom)) {
				res[++i] = lit.getSMTFormula(smtTheory);
			}
		}
		return res;
	}

	public class AllSatIterator implements Iterator<Term[]> {

		private final Literal[] mPreds;
		private final Term[] mTerms;
		private Literal[] mBlocker;
		private int mBlockerSize;

		public AllSatIterator(final Literal[] preds, final Term[] terms) {
			mPreds = preds;
			mTerms = terms;
			assert mPreds.length == mTerms.length;
			for (final Literal l : preds) {
				if (!(l.getAtom() instanceof TrueAtom)) {
					++mBlockerSize;
				}
			}
		}

		@Override
		public boolean hasNext() {
			if (mBlocker != null) {
				final Clause conflict = new Clause(mBlocker, mPushPopLevel);
				if (explain(conflict)) {
					return false;
				}
			}
			if (solve() && hasModel()) {
				return true;
			}
			return false;
		}

		@Override
		public Term[] next() {
			final Term[] res = new Term[mPreds.length];
			mBlocker = new Literal[mBlockerSize];
			for (int i = 0; i < mPreds.length; ++i) {
				final Literal l = mPreds[i];
				if (!(l.getAtom() instanceof TrueAtom)) {
					mBlocker[i] = l.getAtom().mDecideStatus.negate();
				}
				res[i] = l.getAtom().mDecideStatus == l ? mTerms[i] : mTerms[i].getTheory().term("not", mTerms[i]);
			}
			return res;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException("Cannot remove model!");
		}

	}

	public boolean isTerminationRequested() {
		if (mCompleteness == INCOMPLETE_CANCELLED || mCancel.isTerminationRequested()) {
			mCompleteness = INCOMPLETE_CANCELLED;
			return true;
		}
		return false;
	}

	/**
	 * Remove all assumptions. We backtrack to level 0.
	 */
	public void clearAssumptions() {
		/* check if we need to clear any assumptions */
		if (mCurrentDecideLevel == 0) {
			return;
		}
		startBacktrack();
		mAssumptionLiterals.clear();
		mLogger.debug("Clearing Assumptions (Baselevel is %d)", mBaseLevel);
		while (mCurrentDecideLevel > 0) {
			final Literal lit = mDPLLStack.remove(mDPLLStack.size() - 1);
			backtrackLiteral(lit);
		}
		assert mCurrentDecideLevel == 0;
		mBaseLevel = 0;
		/* clear unsat clause, if it has assumptions */
		if (mUnsatClause != null && mUnsatClause.getSize() > 0) {
			mUnsatClause = null;
		}

		final Clause conflict = finalizeBacktrack();
		if (conflict != null) {
			explain(conflict);
		}
	}

	/**
	 * Add some literals and prepare for a check-sat. Trivial inconsistencies
	 * between assumptions are detected.
	 *
	 * @param lits The literals to assume.
	 * @return <code>false</code> if the assumptions are trivially inconsistent.
	 */
	public boolean assume(final Literal[] lits) {
		assert mCurrentDecideLevel == mBaseLevel;
		for (final Literal lit : lits) {
			mLogger.debug("Assuming Literal %s", lit);
			mAssumptionLiterals.add(lit);
			// First check if the literal is already set
			if (lit.getAtom().getDecideStatus() != null) {
				if (lit.getAtom().getDecideStatus() == lit) {
					mLogger.debug("Already set!");
					continue;
				} else {
					// We have the assumption lit, but we know ~lit holds.
					// Build the unsatClause from the level0 proof.
					if (mAssumptionLiterals.contains(lit.negate())) {
						mUnsatClause = new Clause(new Literal[] { lit }, new LeafNode(LeafNode.ASSUMPTION, null));
					} else {
						mUnsatClause = getLevel0(lit.negate());
					}
					assert checkValidUnsatClause();
					assert mBaseLevel == mCurrentDecideLevel;
					return false;
				}
			}
			// The literal is not already set => decide it to true
			increaseDecideLevel();
			final Clause conflict = setLiteral(lit);
			mBaseLevel = mCurrentDecideLevel;
			if (conflict != null) {
				mLogger.debug("Conflict when setting literal");
				startBacktrack();
				mUnsatClause = explainConflict(conflict);
				checkValidUnsatClause();
				finalizeBacktrack();
				return false;
			}
		}
		mLogger.debug("Setting base level to %d", mCurrentDecideLevel);
		return true;
	}

	private boolean checkValidUnsatClause() {
		if (mUnsatClause != null) {
			for (final Literal lit : mUnsatClause.mLiterals) {
				assert mAssumptionLiterals.contains(lit.negate()) : "Not an assumption in unsat clause";
			}
		}
		return true;
	}

	/**
	 * Randomly mess with the activity of Atoms, such that the Engine does not prefer atoms that have been active/inactive
	 * so far.
	 */
	public void messWithActivityOfAtoms(final Random rnd) {
		mAtoms.clear();
		for (final DPLLAtom atom : mAtomList) {
			atom.mActivity = atom.mActivity + rnd.nextDouble() * mAtomScale;
			if (atom.mDecideStatus == null) {
				mAtoms.add(atom);
			}
		}
	}
}
