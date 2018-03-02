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
	private int mStacklevel = 0;
	/**
	 * The assertion stack data.
	 */
	private StackData mPpStack;
	/**
	 * List of all input clauses. This list should not contain any learned clauses!
	 */
	private final SimpleList<Clause> mClauses = new SimpleList<Clause>();

	/**
	 * Empty clause. This is a cache that speeds up detecting unsatisfiability in the case our proof does not depend on
	 * a newly pushed formula.
	 */
	private Clause mUnsatClause = null;

	/**
	 * The literals assumed in the last check-sat-assuming call.
	 */
	private Set<Literal> mAssumptionLiterals = new LinkedHashSet<>();

	/* Statistics */
	private int mConflicts, mDecides, mTProps, mProps;
	private int mNumSolvedAtoms, mNumClauses, mNumAxiomClauses;
	SimpleList<Clause> mLearnedClauses = new SimpleList<Clause>();
	private long mPropTime, mPropClauseTime, mExplainTime;
	private long mSetTime, mCheckTime, mBacktrackTime;
	private final Theory mSmtTheory;
	private int mNumRandomSplits;

	private boolean mHasModel;

	double mAtomScale = 1 - 1.0 / Config.ATOM_ACTIVITY_FACTOR;
	double mClsScale = 1 - 1.0 / Config.CLS_ACTIVITY_FACTOR;

	/**
	 * The list of unit clauses that are not yet decided.
	 */
	WatchList mWatcherSetList = new WatchList();
	WatchList mWatcherBackList = new WatchList();

	ArrayList<Literal> mDecideStack = new ArrayList<Literal>();

	/**
	 * The list of all theories.
	 */
	private ITheory[] mTheories = new ITheory[0];
	private final AtomQueue mAtoms = new AtomQueue();

	private int mCurrentDecideLevel = 0;
	private int mBaseLevel = 0;
	private boolean mPGenabled = false;
	private boolean mProduceAssignments = false;
	private ScopedHashMap<String, Literal> mAssignments;

	// Random source for the solver.
	private final Random mRandom;

	private final TerminationRequest mCancel;

	public DPLLEngine(final Theory smtTheory, final LogProxy logger, final TerminationRequest cancel) {
		mSmtTheory = smtTheory;
		mCompleteness = COMPLETE;
		assert logger != null;
		mLogger = logger;
		mPpStack = new NonRootLvlStackData(null);
		// Benchmark sets the seed...
		mRandom = new Random();
		mCancel = cancel;
	}

	public int getDecideLevel() {
		return mCurrentDecideLevel;
	}

	public void insertPropagatedLiteral(final ITheory t, final Literal lit, final int decideLevel) {
		assert lit.getAtom().mDecideStatus == null;
		assert !mDecideStack.contains(lit);
		assert !mDecideStack.contains(lit.negate());
		assert t != null : "Decision in propagation!!!";
		assert checkDecideLevel();
		int stackptr = mDecideStack.size();
		int level = mCurrentDecideLevel;
		while (level > decideLevel) {
			final DPLLAtom atom = mDecideStack.get(--stackptr).getAtom();
			if (atom.mExplanation == null) {
				level--;
			}
			atom.mStackPosition++;
		}
		mDecideStack.add(stackptr, lit);
		final DPLLAtom atom = lit.getAtom();
		// We have to tell the ppStack about this literal. Otherwise it will
		// not be removed on a pop
		mPpStack.addAtom(atom);
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
		assert mDecideStack.get(beforeAtom.getStackPosition()).getAtom() == beforeAtom;
		assert beforeAtom.mDecideStatus != null;
		assert beforeAtom.getStackPosition() >= 0;
		assert lit.getAtom().mDecideStatus == null;
		assert !mDecideStack.contains(lit);
		assert !mDecideStack.contains(lit.negate());
		assert t != null : "Decision in propagation!!!";
		assert checkDecideLevel();
		final int stackptr = beforeAtom.getStackPosition();
		int level = beforeAtom.getDecideLevel();
		if (beforeAtom.mExplanation == null) {
			level--;
		}
		mDecideStack.add(stackptr, lit);
		for (int i = stackptr + 1; i < mDecideStack.size(); i++) {
			assert mDecideStack.get(i).getAtom().getStackPosition() == i - 1;
			mDecideStack.get(i).getAtom().mStackPosition = i;
		}
		final DPLLAtom atom = lit.getAtom();
		// We have to tell the ppStack about this literal. Otherwise it will
		// not be removed on a pop
		mPpStack.addAtom(atom);
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
			final int level = mDecideStack.size(); // NOPMD
			conflict = propagateClauses();
			if (conflict != null) {
				return conflict;
			}
			if (mDecideStack.size() > level) {
				continue;
			}

			long time = 0;
			if (Config.PROFILE_TIME) {
				time = System.nanoTime();
			}
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
			if (mDecideStack.size() == level) {
				return null;
			}
		}
	}

	private Clause propagateTheories() {
		while (true) {
			boolean changed = false;
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

	private Clause propagateClauses() {
		long time = 0;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime() - mSetTime;
		}
		while (!mWatcherBackList.isEmpty()) {
			final int index = mWatcherBackList.mHeadIndex;
			Clause clause = mWatcherBackList.removeFirst();
			/* check if clause was already removed */
			if (clause.mNext == null) {
				// System.err.println("Found removed clause in progation: " + clause);
				continue;
			}
			final Literal[] lits = clause.mLiterals;
			final Literal myLit = lits[index];
			final Literal status = myLit.getAtom().mDecideStatus;
			/* Special case unit clause: propagate or return as conflict clause */
			if (lits.length == 1) {
				myLit.getAtom().mBacktrackWatchers.append(clause, index);
				if (status != myLit) {
					if (status == null) {
						/* Propagate the unit clause. */
						myLit.getAtom().mExplanation = clause;
						mProps++;
						clause = setLiteral(myLit);
					}
					if (Config.PROFILE_TIME) {
						mPropClauseTime += System.nanoTime() - time - mSetTime;
					}
					return clause;
				}
			} else if (status == myLit.negate()) {
				mWatcherSetList.append(clause, index);
			} else {
				myLit.mWatchers.append(clause, index);
			}
		}

		// logger.info("new set: "+watcherSetList.size());
		nextList: while (!mWatcherSetList.isEmpty()) {
			final int index = mWatcherSetList.getIndex();
			Clause clause = mWatcherSetList.removeFirst();
			/* check if clause was already removed */
			if (clause.mNext == null) {
				continue nextList;
			}
			final Literal[] lits = clause.mLiterals;
			assert lits[index].getAtom().mDecideStatus == lits[index].negate();
			assert lits.length >= 2;
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
			 * Now we haven't found another atom to watch. Hence we have a unit clause or conflict clause.
			 */
			// put the entry back into the watch list of the literal. Until
			// the literal changes again, the watcher is not needed anymore.
			lits[index].mWatchers.append(clause, index);
			if (otherAtom.mDecideStatus == null) {
				/* Propagate the unit clause. */
				otherAtom.mExplanation = clause;
				mProps++;
				clause = setLiteral(otherLit);
				if (clause == null) {
					clause = propagateTheories();
				}
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
	 * Sets a literal to true and tells all theories about it. The literal must be undecided when this function is
	 * called.
	 *
	 * @param literal
	 *            the literal to set.
	 * @return a conflict clause if a conflict was detected.
	 */
	@SuppressWarnings("unused")
	private Clause setLiteral(final Literal literal) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("S " + literal);
		}
		final DPLLAtom atom = literal.getAtom();
		assert atom.mDecideStatus == null;
		assert mAtoms.contains(atom);
		atom.mStackPosition = mDecideStack.size();
		mDecideStack.add(literal);
		atom.mDecideLevel = mCurrentDecideLevel;
		atom.mDecideStatus = literal;
		atom.mLastStatus = atom.mDecideStatus;
		mAtoms.remove(atom);
		assert !Config.EXPENSIVE_ASSERTS || checkDecideLevel();
		mWatcherSetList.moveAll(literal.negate().mWatchers);
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
				// Make sure the unit literal is actually a unit
				if (mAssumptionLiterals.contains(clause.getLiteral(0).negate())) {
					mUnsatClause = clause;
					return;
				}
				/* propagate unit clause: only register watcher zero. */
				mWatcherBackList.append(clause, 0);
			}
		} else {
			// Move unset literals upfront
			int dest = 0;
			while (dest < 2) {
				if (mAssumptionLiterals.contains(clause.getLiteral(dest).negate())) {
					boolean found = false;
					for (int i = dest + 1; i < clause.getSize(); ++i) {
						if (!mAssumptionLiterals.contains(clause.getLiteral(i).negate())) {
							// swap literal @dest with literal @i
							final Literal tmp = clause.mLiterals[i];
							clause.mLiterals[i] = clause.mLiterals[dest];
							clause.mLiterals[dest] = tmp;
							found = true;
							break;
						}
					}
					if (found) {
						dest++;
					} else if (dest == 0) {
						// We only found assumptions in this clause.
						mUnsatClause = clause;
						return;
					} else {
						assert dest == 1;
						// We found a unit clause
						/* propagate unit clause: only register watcher zero. */
						mWatcherBackList.append(clause, 0);
						return;
					}
				} else {
					dest++;
				}
			}
			/*
			 * A clause is "watched" if it appears on either the watcherBack/SetList or the watchers list of some atom.
			 */
			mWatcherBackList.append(clause, 0);
			mWatcherBackList.append(clause, 1);
		}
	}

	public void addClause(final Clause clause) {
		mAtomScale += 1.0 - 1.0 / Config.ATOM_ACTIVITY_FACTOR;
		clause.mActivity = Double.POSITIVE_INFINITY;
		mNumAxiomClauses++;
		assert clause.mStacklevel == mStacklevel;
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
		final Clause clause = new Clause(literals, mStacklevel);
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
		for (final Literal lit : mDecideStack) {
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
		int stackPtr = mDecideStack.size();
		while (true) {
			final Literal lit = mDecideStack.get(--stackPtr);
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
	 * Explain one conflict clause. DO NOT CALL THIS FUNCTION DIRECTLY!!! USE {@link #explain(Clause)} INSTEAD SINCE
	 * THIS FUNCTION DOES A CORRECT LOOP INCLUDING {@link #finalizeBacktrack()} AND HENCE DOES NOT LEAVE BEHIND
	 * INCONSISTENT THEORY SOLVERS.
	 *
	 * @param clause
	 *            Conflict clause
	 * @return Explanation
	 */
	private Clause explainConflict(final Clause clause) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("explain conflict " + clause);
		}
		final HashSet<Literal> level0Ants = new HashSet<Literal>();
		List<Antecedent> antecedents = null;
		if (isProofGenerationEnabled()) {
			antecedents = new ArrayList<Antecedent>();
		}
		int expstacklevel = clause.mStacklevel;
		mConflicts++;
		assert checkDecideLevel();
		mAtomScale *= Config.ATOM_ACTIVITY_FACTOR;
		mClsScale *= Config.CLS_ACTIVITY_FACTOR;
		final Set<Literal> conflict = new CuckooHashSet<Literal>();
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
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("removing level0: " + conflict);
		}
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
			final Literal lit = mDecideStack.remove(mDecideStack.size() - 1);
			assert !conflict.contains(lit.negate());
			assert !conflict.contains(lit);
			if (lit.getAtom().mExplanation == null) {
				decreaseDecideLevel();
			}
			assert checkDecideLevel();
			backtrackLiteral(lit);
			assert checkDecideLevel();
		}
		while (numLitsOnMaxDecideLevel > 1) {
			assert checkDecideLevel();
			assert mCurrentDecideLevel == maxDecideLevel;
			assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
			assert checkDecideLevel();
			final Literal lit = mDecideStack.get(mDecideStack.size() - 1);
			assert !conflict.contains(lit.negate());
			if (!conflict.contains(lit)) {
				assert lit.getAtom().mExplanation != null;
				assert checkDecideLevel();
				mDecideStack.remove(mDecideStack.size() - 1);
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
			mDecideStack.remove(mDecideStack.size() - 1);
			backtrackLiteral(lit);
			assert checkDecideLevel();
			conflict.remove(lit);
			numLitsOnMaxDecideLevel--;
			final DPLLAtom atom = lit.getAtom();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Resolving with " + expl + " pivot = " + atom);
			}
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
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("new conflict: " + conflict);
			}
		}
		assert mCurrentDecideLevel == maxDecideLevel;
		assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
		assert numLitsOnMaxDecideLevel == 1;
		while (mCurrentDecideLevel >= maxDecideLevel) {
			final Literal lit = mDecideStack.remove(mDecideStack.size() - 1);
			assert !conflict.contains(lit.negate());
			if (lit.getAtom().mExplanation == null) {
				decreaseDecideLevel();
			}
			assert checkDecideLevel();
			backtrackLiteral(lit);
			assert checkDecideLevel();
		}
		/*
		 * We removed at least one decision point. Try to backtrack further.
		 */
		if (Config.DEEP_BACKTRACK) {
			findBacktrackingPoint(conflict);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Backtrack to " + mDecideStack.size());
		}

		final HashMap<Literal, Integer> redundancy = computeRedundancy(conflict);
		final Integer REDUNDANT = 1;

		int stackPtr = mDecideStack.size();
		while (stackPtr > mNumSolvedAtoms) {
			final Literal lit = mDecideStack.get(--stackPtr);
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
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("removing redundancy yields " + conflict);
		}
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
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Resolved to " + resolution);
		}
		// If resolution size is number of literals we are unsat
		if (newlits.length == numAssumptions) {
			mUnsatClause = resolution;
		}
		return resolution;
	}

	/**
	 * Explain all conflicts currently present in the solver starting with a given initial conflict. Returns
	 * <code>true</code> if and only if the empty clause has been derived.
	 *
	 * @param conflict
	 *            The initial conflict.
	 * @return Is the solver inconsistent?
	 */
	private boolean explain(Clause conflict) {
		while (conflict != null) {
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
		final HashMap<Literal, Integer> status = new HashMap<Literal, Integer>();
		for (final Literal l : conflict) {
			if (l.getAtom().getDecideStatus() != null) {
				assert l.getAtom().getDecideStatus() == l;
				status.put(l, REDUNDANT);
			}
		}
		final ArrayDeque<Literal> todo = new ArrayDeque<Literal>();
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

	private Clause finalizeBacktrack() {
		mWatcherBackList.moveAll(mWatcherSetList);
		for (final ITheory t : mTheories) {
			final Clause conflict = t.backtrackComplete();
			if (conflict != null) {
				return conflict;
			}
		}
		return null;
	}

	private void findBacktrackingPoint(final Set<Literal> conflict) {
		int i = mDecideStack.size();
		while (i > 0) {
			final Literal lit = mDecideStack.get(--i);
			if (conflict.contains(lit)) {
				break;
			}
			if (lit.getAtom().mExplanation == null) {
				while (mDecideStack.size() > i) {
					backtrackLiteral(mDecideStack.remove(mDecideStack.size() - 1));
				}
				decreaseDecideLevel();
			}
		}
	}

	private void backtrackLiteral(final Literal literal) {
		long time;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("B " + literal);
		}
		final DPLLAtom atom = literal.getAtom();
		mWatcherBackList.moveAll(atom.mBacktrackWatchers);
		atom.mExplanation = null;
		atom.mDecideStatus = null;
		atom.mDecideLevel = -1;
		atom.mStackPosition = -1;
		mAtoms.add(atom);
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		for (final ITheory t2 : mTheories) {
			t2.backtrackLiteral(literal);
		}
		if (Config.PROFILE_TIME) {
			mBacktrackTime += System.nanoTime() - time;
		}
	}

	private Clause checkConsistency() {
		long time = 0;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		for (final ITheory t : mTheories) {
			final Clause conflict = t.computeConflictClause();
			if (conflict != null) {
				return conflict;
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
			mLogger.info("Atoms: " + mNumSolvedAtoms + "/" + (mAtoms.size() + mDecideStack.size()) + " Clauses: "
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
				final Map<Literal, Double> scores = new HashMap<Literal, Double>();
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
					atom.setPreferredStatus(Pscore > Nscore ? atom : atom.negate());
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
							if (!suggested && mWatcherBackList.isEmpty() && mAtoms.isEmpty()) {
								/* We found a model */
								if (mLogger.isInfoEnabled()) {
									printStatistics();
									mLogger.info("Hooray, we found a model:");
									for (final ITheory t : mTheories) {
										t.dumpModel(mLogger);
									}
									if (mLogger.isTraceEnabled()) {
										for (final Literal dlit : mDecideStack) {
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
					for (final Literal l : mDecideStack) {
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
					final DPLLAtom next = mAtoms.peek();
					int restartpos = -1;
					for (int i = mNumSolvedAtoms + mBaseLevel; i < mDecideStack.size(); ++i) {
						final DPLLAtom var = mDecideStack.get(i).getAtom();
						if (var.mExplanation == null && var.mActivity < next.mActivity) {
							// This has been a decision
							restartpos = i;
							break;
						}
					}
					int decleveldec = 0;
					if (restartpos != -1) {
						while (mDecideStack.size() > restartpos) {
							final Literal lit = mDecideStack.remove(mDecideStack.size() - 1);
							assert lit.getAtom().mDecideLevel != mBaseLevel;
							final Object litexpl = lit.getAtom().mExplanation;
							if (litexpl == null) {
								++decleveldec;
							}
							if (litexpl instanceof Clause) {
								((Clause) litexpl).mActivity += mClsScale;
								// ((Clause) litexpl).usedTimes++;
							}
							backtrackLiteral(lit);
						}
					}
					unlearnClauses(mStacklevel);
					conflict = finalizeBacktrack();
					assert conflict == null;
					mCurrentDecideLevel -= decleveldec;
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
		} catch (final RuntimeException eUnknown) {
			if (System.getProperty("smtinterpol.ddfriendly") != null) {
				System.exit(3);
			}
			throw eUnknown;
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
		mPpStack.addAtom(atom);
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

	public Theory getSMTTheory() {
		return mSmtTheory;
	}

	public String dumpClauses() {
		final StringBuilder sb = new StringBuilder();
		for (final Clause c : mClauses) {
			sb.append("(assert ");
			final Literal[] lits = c.mLiterals;
			if (lits.length == 1) {
				sb.append(lits[0].getSMTFormula(mSmtTheory)).append(")\n");
			} else {
				sb.append("(or");
				for (final Literal l : lits) {
					sb.append(' ').append(l.getSMTFormula(mSmtTheory));
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
		mPpStack = mPpStack.save(this);
		if (mAssignments != null) {
			mAssignments.beginScope();
		}
		++mStacklevel;
	}

	public void pop(final int numpops) {
		if (numpops < 1 || numpops > mStacklevel) {
			throw new IllegalArgumentException("Must pop a positive number less than the current stack level");
		}
		final int targetstacklevel = mStacklevel - numpops;
		if (mUnsatClause != null && mUnsatClause.mStacklevel > targetstacklevel) {
			mUnsatClause = null;
		}
		if (Config.EXPENSIVE_ASSERTS && !checkProofStackLevel(mUnsatClause, targetstacklevel)) {
			throw new AssertionError();
		}
		if (!mDecideStack.isEmpty()) {
			final java.util.ListIterator<Literal> literals = mDecideStack.listIterator(mDecideStack.size());
			while (literals.hasPrevious()) {
				final Literal lit = literals.previous();
				final Object litexpl = lit.getAtom().mExplanation;
				if (litexpl instanceof Clause) {
					((Clause) litexpl).mActivity += mClsScale;
					// ((Clause) litexpl).usedTimes++;
				}
				backtrackLiteral(lit);
			}
			mDecideStack.clear();
			final Clause conflict = finalizeBacktrack();
			assert conflict == null;
		}
		unlearnClauses(targetstacklevel);
		mCurrentDecideLevel = 0;
		mNumSolvedAtoms = 0;
		final Iterator<Clause> inputit = mClauses.iterator();
		while (inputit.hasNext()) {
			final Clause input = inputit.next();
			if (input.mStacklevel > targetstacklevel) {
				if (input.doCleanup(this)) {
					inputit.remove();
				} else {
					throw new InternalError("Input clause still blocked, but invalid");
					// logger.debug("Removed clause {0}", input);
				}
			} else {
				// Terminate iteration here since only clauses with lower
				// stacklevel remain.
				// logger.debug("Keeping input {0}", input);
				break;
			}
		}
		for (int i = 0; i < numpops; ++i) {
			mPpStack = mPpStack.restore(this, mStacklevel - i - 1);
		}
		mStacklevel = targetstacklevel;
		if (mAssignments != null) {
			for (int i = 0; i < numpops; ++i) {
				if (mAssignments.getActiveScopeNum() == 1) {
					break;
				}
				mAssignments.endScope();
			}
		}
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

	private final void increaseDecideLevel() {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Decide@" + mDecideStack.size());
		}
		mCurrentDecideLevel++;
		assert mCurrentDecideLevel >= 0 : "Decidelevel negative";
		for (final ITheory t : mTheories) {
			t.increasedDecideLevel(mCurrentDecideLevel);
		}
	}

	private final void decreaseDecideLevel() {
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
		return mStacklevel;
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
		// Don't crash the solver one stupid scripts...
		final Object[] res = mTheories == null ? new Object[1] : new Object[mTheories.length + 1];
		final Object[] mystats = new Object[][] { { "Conflicts", mConflicts }, { "Propagations", mProps },
				{ "Theory_propagations", mTProps }, { "Decides", mDecides }, { "Random_splits", mNumRandomSplits },
				{ "Num_Atoms", mAtoms.size() + mDecideStack.size() }, { "Solved_Atoms", mNumSolvedAtoms },
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
		final boolean old = mProduceAssignments;
		mProduceAssignments = value;
		if (old != mProduceAssignments) {
			if (old) {
				mAssignments = null;
			} else {
				mAssignments = new ScopedHashMap<String, Literal>();
			}
		}
	}

	public boolean isProduceAssignments() {
		return mProduceAssignments;
	}

	public void trackAssignment(final String label, final Literal literal) {
		mAssignments.put(label, literal);
	}

	public Assignments getAssignments() {
		if (!mProduceAssignments) {
			return null;
		}
		final HashMap<String, Boolean> assignment = new HashMap<String, Boolean>(mAssignments.size(), 1.0f);
		for (final Map.Entry<String, Literal> me : mAssignments.entrySet()) {
			assignment.put(me.getKey(), me.getValue().getAtom().mDecideStatus == me.getValue());
		}
		return new Assignments(assignment);
	}

	/**
	 * Run a quick and incomplete check on the current context. This only uses propagations and a conflict explanation
	 * to the empty clause.
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
	 * Propagate as much as possible. In contrast to {@link #quickCheck()}, this function tells the theory solvers to
	 * start a check. This might get more propagations than {@link #quickCheck()}.
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
		while (mDecideStack.size() > mBaseLevel + mNumSolvedAtoms) {
			final Literal lit = mDecideStack.remove(mDecideStack.size() - 1);
			backtrackLiteral(lit);
			// Flip the decision
			lit.getAtom().mLastStatus = lit.negate();
		}
		final Clause conflict = finalizeBacktrack();
		assert conflict == null;
		mCurrentDecideLevel = mBaseLevel;
	}

	public void flipNamedLiteral(final String name) throws SMTLIBException {
		while (mDecideStack.size() > mBaseLevel + mNumSolvedAtoms) {
			final Literal lit = mDecideStack.remove(mDecideStack.size() - 1);
			backtrackLiteral(lit);
		}
		final Clause conflict = finalizeBacktrack();
		assert conflict == null;
		mCurrentDecideLevel = mBaseLevel;
		final Literal lit = mAssignments.get(name);
		if (lit == null) {
			throw new SMTLIBException("Name " + name + " not known");
		}
		final DPLLAtom atom = lit.getAtom();
		atom.mLastStatus = atom.mLastStatus == null ? atom : atom.mLastStatus.negate();
	}

	/**
	 * Returns the list of all input clauses. This list does not contain any learned clauses!
	 */
	public SimpleList<Clause> getClauses() {
		return mClauses;
	}

	public Term[] getSatisfiedLiterals() {
		int size = 0;
		for (final Literal lit : mDecideStack) {
			if (!(lit.getAtom() instanceof NamedAtom)) {
				++size;
			}
		}
		final Term[] res = new Term[size];
		int i = -1;
		for (final Literal lit : mDecideStack) {
			if (!(lit.getAtom() instanceof NamedAtom)) {
				res[++i] = lit.getSMTFormula(mSmtTheory, true);
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
				final Clause conflict = new Clause(mBlocker, mStacklevel);
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
				res[i] = l.getAtom().mDecideStatus == l ? mTerms[i] : getSMTTheory().term("not", mTerms[i]);
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
		if (mBaseLevel == 0) {
			return;
		}
		mAssumptionLiterals.clear();
		mLogger.debug("Clearing Assumptions (Baselevel is %d)", mBaseLevel);
		while (!mDecideStack.isEmpty()) {
			final Literal top = mDecideStack.get(mDecideStack.size() - 1);
			if (top.getAtom().getDecideLevel() == 0) {
				break;
			}
			mDecideStack.remove(mDecideStack.size() - 1);
			backtrackLiteral(top);
		}
		mBaseLevel = 0;
		mCurrentDecideLevel = 0;
		mUnsatClause = finalizeBacktrack();
	}

	/**
	 * Add some literals and prepare for a check-sat. Trivial inconsistencies between assumptions are detected.
	 *
	 * @param lits
	 *            The literals to assume.
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
						mUnsatClause = new Clause(new Literal[] { lit },
								new LeafNode(LeafNode.ASSUMPTION, null));
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
}
