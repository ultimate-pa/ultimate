/*
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermCompiler;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.DestructiveEqualityReasoning.DERResult;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching.EMatching;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;

/**
 * Solver for quantified formulas within the almost uninterpreted fragment (Restrictions on terms and literals are
 * explained in the corresponding classes. For reference, see Ge & de Moura, 2009).
 *
 * For formulas outside the fragment, the solver may still find a proof of unsatisfiability but SMTInterpol will not
 * return {@code satisfiable} in this case.
 *
 * This solver may be merged with the EPR solver implementation by Alexander Nutz in the future; for now, we keep it
 * separate.
 *
 * @author Tanja Schindler
 */
public class QuantifierTheory implements ITheory {

	private final Clausifier mClausifier;
	private final LogProxy mLogger;
	private final Theory mTheory;
	private final DPLLEngine mEngine;

	final CClosure mCClosure;
	final LinArSolve mLinArSolve;

	private final EMatching mEMatching;
	private final InstantiationManager mInstantiationManager;
	private final Map<Sort, Term> mLambdas;

	/**
	 * Clauses that only the QuantifierTheory knows, i.e. that contain at least one literal with an (implicitly)
	 * universally quantified variable.
	 */
	private final ScopedArrayList<QuantClause> mQuantClauses;

	/**
	 * Instances of quantified clauses that may be added to the DPLL engine in the future. The keys are undecided
	 * literals (not atoms!) mapped to the instances they are contained in. The instances must not contain literals that
	 * are currently set to true. This map should be used to return conflicts or propagate literals when an InstClause
	 * becomes a conflict or unit clause.
	 */
	private final Map<Literal, Set<InstClause>> mPendingInstances;

	// Statistics
	long mNumInstancesProduced, mNumInstancesDER, mNumInstancesProducedConfl, mNumInstancesProducedEM,
			mNumInstancesProducedEnum;
	private long mNumCheckpoints, mNumCheckpointsWithNewEval, mNumConflicts, mNumProps, mNumFinalcheck;
	private long mCheckpointTime, mFindEmatchingTime, mFinalCheckTime, mEMatchingTime, mDawgTime;
	int[] mNumInstancesOfAge, mNumInstancesOfAgeEnum;

	// Options
	InstantiationMethod mInstantiationMethod;
	boolean mUseUnknownTermValueInDawgs;
	boolean mPropagateNewAux;
	boolean mPropagateNewTerms;

	public QuantifierTheory(final Theory th, final DPLLEngine engine, final Clausifier clausifier,
			final InstantiationMethod instMethod, final boolean useUnknownTermDawgs, final boolean propagateNewTerms,
			final boolean propagateNewAux) {
		mClausifier = clausifier;
		mLogger = clausifier.getLogger();
		mTheory = th;
		mEngine = engine;

		mInstantiationMethod = instMethod;
		mUseUnknownTermValueInDawgs = useUnknownTermDawgs;
		mPropagateNewTerms = propagateNewTerms;
		mPropagateNewAux = propagateNewAux;

		mCClosure = clausifier.getCClosure();
		mLinArSolve = clausifier.getLASolver();

		mEMatching = new EMatching(this);
		mInstantiationManager = new InstantiationManager(this);
		mLambdas = new HashMap<>();

		mQuantClauses = new ScopedArrayList<>();

		mPendingInstances = new LinkedHashMap<>();

		mNumInstancesOfAge = new int[Integer.SIZE];
		mNumInstancesOfAgeEnum = new int[Integer.SIZE];
	}

	@Override
	public Clause startCheck() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void endCheck() {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause setLiteral(final Literal literal) {
		if (mQuantClauses.isEmpty()) {
			assert mPendingInstances.isEmpty();
			return null;
		}
		// Remove clauses that have become true from potential conflict and unit clauses.
		if (mPendingInstances.containsKey(literal)) {
			for (final InstClause instClause : mPendingInstances.remove(literal)) {
				assert instClause.mLits.contains(literal);
				for (final Literal otherLit : instClause.mLits) {
					if (otherLit != literal) {
						final Set<InstClause> clauses = mPendingInstances.get(otherLit);
						if (clauses != null) {
							clauses.remove(instClause);
							if (clauses.isEmpty()) {
								mPendingInstances.remove(otherLit);
							}
						}
					}
				}
			}
		}
		// Remove former undef negated lit (now false) from map and decrease number of undef lits in clauses containing
		// the negated lit.
		if (mPendingInstances.containsKey(literal.negate())) {
			for (final InstClause instClause : mPendingInstances.remove(literal.negate())) {
				assert instClause.mNumUndefLits > 0;
				instClause.mNumUndefLits -= 1;
				if (instClause.isConflict()) {
					assert !Config.EXPENSIVE_ASSERTS || instClause.countAndSetUndefLits() == 0;
					mLogger.debug("Quant conflict: %s", instClause);
					mNumConflicts++;
					return instClause.toClause(mEngine.isProofGenerationEnabled());
				}
			}
		}
		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		// we throw the pending clause instances away after backtracking.
	}

	@Override
	public Clause checkpoint() {
		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		mNumCheckpoints++;
		Clause conflict = null;
		if (!mQuantClauses.isEmpty()) {

			// Don't search for new conflict and unit clauses if there are still potential conflict and unit clauses in
			// the queue.

			// TODO: This does not hold any more when we add instances from final check to the pendingInstances.
			// if (mLinArSolve == null) {
			// assert mPendingInstances.isEmpty() || mInstantiationMethod == InstantiationMethod.E_MATCHING_EAGER
			// || mInstantiationMethod == InstantiationMethod.E_MATCHING_LAZY
			// || mEngine.getDecideLevel() <= mDecideLevelOfLastCheckpoint;
			// }
			if (!mPendingInstances.isEmpty()) {
				return null;
			}

			final Collection<InstClause> potentiallyInterestingInstances;
			switch (mInstantiationMethod) {
			case E_MATCHING_CONFLICT:
				mNumCheckpointsWithNewEval++;
				mEMatching.run();
				potentiallyInterestingInstances = mInstantiationManager.findConflictAndUnitInstancesWithEMatching();
				if (Config.PROFILE_TIME) {
					mFindEmatchingTime += System.nanoTime() - time;
				}
				break;
			case AUF_CONFLICT:
				mNumCheckpointsWithNewEval++;
				potentiallyInterestingInstances = mInstantiationManager.findConflictAndUnitInstances();
				break;
			case E_MATCHING_EAGER:
				mNumCheckpointsWithNewEval++;
				mEMatching.run();
				potentiallyInterestingInstances = mInstantiationManager.computeEMatchingInstances();
				if (Config.PROFILE_TIME) {
					mFindEmatchingTime += System.nanoTime() - time;
				}
				break;
			case E_MATCHING_LAZY:
				// Nothing to do, only in final check
				potentiallyInterestingInstances = null;
				break;
			case E_MATCHING_CONFLICT_LAZY:
				// Nothing to do, only in final check
				potentiallyInterestingInstances = null;
				break;
			default:
				throw new InternalError("Unknown instantiation method");
			}
			conflict = addInstClausesToPending(potentiallyInterestingInstances);
			if (conflict != null) {
				mLogger.debug("Quant conflict: %s", conflict);
				mEngine.learnClause(conflict);
				mNumConflicts++;
			}
		}
		if (Config.PROFILE_TIME) {
			mCheckpointTime += System.nanoTime() - time;
		}
		return conflict;
	}

	@Override
	public Clause computeConflictClause() {
		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		mNumFinalcheck++;
		assert mPendingInstances.isEmpty();
		Clause conflict = null;

		if (!mQuantClauses.isEmpty()) {
			Collection<InstClause> potentiallyInterestingInstances = new LinkedHashSet<>();

			boolean foundNonSat = false;
			if (mInstantiationMethod == InstantiationMethod.E_MATCHING_LAZY) {
				mEMatching.run();
				potentiallyInterestingInstances = mInstantiationManager.computeEMatchingInstances();
				if (Config.PROFILE_TIME) {
					mFindEmatchingTime += System.nanoTime() - time;
				}
				for (final InstClause i : potentiallyInterestingInstances) {
					if (i.countAndSetUndefLits() != -1) {
						// Don't search for other instances if E-matching found one that is not yet satisfied.
						foundNonSat = true;
						break;
					}
				}
			} else if (mInstantiationMethod == InstantiationMethod.E_MATCHING_CONFLICT_LAZY) {
				mEMatching.run();
				potentiallyInterestingInstances = mInstantiationManager.findConflictAndUnitInstancesWithEMatching();
				if (Config.PROFILE_TIME) {
					mFindEmatchingTime += System.nanoTime() - time;
				}
				for (final InstClause i : potentiallyInterestingInstances) {
					if (i.countAndSetUndefLits() != -1) {
						// Don't search for other instances if E-matching based conflict/unit search found one that is
						// not
						// yet satisfied. (The method might miss some true literals, so we need to check this here.)
						foundNonSat = true;
						break;
					}
				}
			}
			if (mClausifier.getEngine().isTerminationRequested()) {
				return null;
			}
			if (potentiallyInterestingInstances.isEmpty() || !foundNonSat) {
				potentiallyInterestingInstances = mInstantiationManager.instantiateSomeNotSat();
			}
			conflict = addInstClausesToPending(potentiallyInterestingInstances);
			if (conflict != null) {
				mNumConflicts++;
				mEngine.learnClause(conflict);
			}
		}
		if (Config.PROFILE_TIME) {
			mFinalCheckTime += System.nanoTime() - time;
		}
		return conflict;
	}

	@Override
	public Literal getPropagatedLiteral() {
		if (mQuantClauses.isEmpty()) {
			assert mPendingInstances.isEmpty();
			return null;
		}

		for (final Map.Entry<Literal, Set<InstClause>> entry : mPendingInstances.entrySet()) {
			if (mEngine.isTerminationRequested()) {
				return null;
			}
			final Literal lit = entry.getKey();
			for (final InstClause inst : entry.getValue()) {
				if (inst.isUnit()) {
					assert !Config.EXPENSIVE_ASSERTS || inst.countAndSetUndefLits() == 1;
					final Clause expl = inst.toClause(mEngine.isProofGenerationEnabled());
					lit.getAtom().mExplanation = expl;
					mEngine.learnClause(expl);
					mNumProps++;
					mLogger.debug("Quant Prop: %s Reason: %s", lit, lit.getAtom().mExplanation);
					return lit;
				} else {
					if (mInstantiationMethod != InstantiationMethod.E_MATCHING_EAGER
							&& mInstantiationMethod != InstantiationMethod.E_MATCHING_LAZY) {
						mLogger.debug("Not propagated: %s Clause: %s", lit, inst.mLits);
					}
				}
			}
		}
		return null;
	}

	@Override
	public Clause getUnitClause(final Literal literal) {
		assert false : "Should never be called.";
		return null;
	}

	@Override
	public Literal getSuggestion() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		logger.info("Quant: DER produced %d ground clause(s).", mNumInstancesDER);
		logger.info("Quant: Instances produced: %d (Conflict/Unit: %d, E-Matching: %d, Enumeration: %d)",
				mNumInstancesProduced, mNumInstancesProducedConfl, mNumInstancesProducedEM, mNumInstancesProducedEnum);
		logger.info(
				"Quant: Subs of age 0, 1, 2-3, 4-7, ... : %s, (Enumeration: %s)", Arrays.toString(mNumInstancesOfAge),
				Arrays.toString(mNumInstancesOfAgeEnum));
		logger.info("Quant: Conflicts: %d Props: %d Checkpoints (with new evaluation): %d (%d) Final Checks: %d",
				mNumConflicts, mNumProps, mNumCheckpoints, mNumCheckpointsWithNewEval, mNumFinalcheck);
		logger.info(
				"Quant times: Checkpoint: %d.%03d Find with E-matching: %d.%03d E-Matching: %d.%03d Dawg: %d.%03d Final Check: %d.%03d",
				mCheckpointTime / 1000 / 1000, mCheckpointTime /1000 % 1000,
				mFindEmatchingTime / 1000 / 1000, mFindEmatchingTime / 1000 % 1000,
				mEMatchingTime / 1000 / 1000, mEMatchingTime / 1000 % 1000,
				mDawgTime / 1000 / 1000, mDawgTime / 1000 % 1000,
				mFinalCheckTime / 1000 / 1000, mFinalCheckTime / 1000 % 1000);
	}

	@Override
	public void dumpModel(final LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public void backtrackAll() {
		mEMatching.removeAllTriggers();
		mInstantiationManager.resetInterestingTerms();
		mPendingInstances.clear();
	}

	@Override
	public void backtrackStart() {
		mPendingInstances.clear();
	}

	@Override
	public Clause backtrackComplete() {
		final int decisionLevel = mClausifier.getEngine().getDecideLevel();
		mEMatching.undo(decisionLevel);
		mInstantiationManager.resetInterestingTerms();
		mInstantiationManager.resetSubsAgeForFinalCheck();
		return null;
	}

	@Override
	public void restart(final int iteration) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
		// TODO Auto-generated method stub

	}

	@Override
	public void push() {
		mQuantClauses.beginScope();
	}

	@Override
	public void pop() {
		assert mPendingInstances.isEmpty(); // backtrackComplete() is called before pop()
		mInstantiationManager.removeAllInstClauses();
		mEMatching.removeAllTriggers();
		for (final QuantClause quantClause : mQuantClauses.currentScope()) {
			mInstantiationManager.removeClause(quantClause);
			mEMatching.removeClause(quantClause);
		}
		mQuantClauses.endScope();
		mEMatching.reAddClauses(mQuantClauses);
	}

	@Override
	public Object[] getStatistics() {
		return new Object[] { ":Quant", new Object[][] { { "DER ground results", mNumInstancesDER },
			{ "Instances produced", mNumInstancesProduced },
			{ "thereof by conflict/unit search", mNumInstancesProducedConfl },
			{ "and by E-matching", mNumInstancesProducedEM }, { "and by enumeration", mNumInstancesProducedEnum },
			{ "Subs of age 0, 1, 2-3, 4-7, ...", Arrays.toString(mNumInstancesOfAge) },
			{ "thereof for enumeration", Arrays.toString(mNumInstancesOfAgeEnum) }, { "Conflicts", mNumConflicts },
			{ "Propagations", mNumProps }, { "Checkpoints", mNumCheckpoints },
			{ "Checkpoints with new evaluation", mNumCheckpointsWithNewEval }, { "Final Checks", mNumFinalcheck },
			{ "Times",
				new Object[][] { { "Checkpoint", mCheckpointTime }, { "Find E-matching", mFindEmatchingTime },
				{ "E-Matching", mEMatchingTime }, { "Final Check", mFinalCheckTime } } } } };
	}

	public QuantAuxEquality createAuxLiteral(final Term auxTerm, final Term definingTerm,
			final SourceAnnotation source) {
		final QuantAuxEquality atom = new QuantAuxEquality(auxTerm, mTheory.mTrue, definingTerm);

		// The atom is almost uninterpreted.
		atom.mIsEssentiallyUninterpreted = atom.negate().mIsEssentiallyUninterpreted = true;
		return atom;
	}

	public ILiteral createAuxFalseLiteral(final QuantAuxEquality auxTrueLit, final SourceAnnotation source) {
		final Term auxTerm = auxTrueLit.getLhs();
		final QuantLiteral atom = new QuantAuxEquality(auxTerm, mTheory.mFalse, auxTrueLit.getDefinition());

		// The atom is almost uninterpreted.
		atom.mIsEssentiallyUninterpreted = atom.negate().mIsEssentiallyUninterpreted = true;
		return atom;
	}

	/**
	 * This method builds new QuantEquality atoms and simultaneously checks if they lie in the almost uninterpreted
	 * fragment, i.e., if they are of the form (i) (euEUTerm = euTerm), pos. and neg. or (ii) (var = ground), integer
	 * only, or if they can be used for DER, i.e. (var != term[withoutthisvar])
	 * <p>
	 * This method also brings equality atoms in the form (var = term), if there exists a TermVariable at top level. For
	 * integers, only if the variable has factor ±1; for reals always.
	 *
	 * @param lhs
	 *            the left side of the equality.
	 * @param rhs
	 *            the right side of the equality.
	 * @return a QuantEquality atom for the equality lhs = rhs.
	 */
	public QuantLiteral getQuantEquality(final Term lhs, final Term rhs, final SourceAnnotation source) {
		// Bring atom to form (var = term) if there exists a variable at "top level".
		Term newLhs = lhs;
		Term newRhs = rhs;
		if (!lhs.getSort().isNumericSort()) {
			final TermVariable leftVar = lhs instanceof TermVariable ? (TermVariable) lhs : null;
			final TermVariable rightVar = rhs instanceof TermVariable ? (TermVariable) rhs : null;
			if (leftVar == null && rightVar != null) {
				newLhs = rightVar;
				newRhs = lhs;
			}
		} else {
			final Polynomial linAdded = new Polynomial(lhs);
			linAdded.add(Rational.MONE, rhs);
			linAdded.mul(linAdded.getGcd().inverse());
			Rational fac = Rational.ONE;
			for (final Map<Term, Integer> smd : linAdded.getSummands().keySet()) {
				Term singleton = null;
				if (smd.size() == 1 && smd.values().iterator().next() == 1) {
					singleton = smd.keySet().iterator().next();
				}
				if (singleton instanceof TermVariable) {
					fac = linAdded.getSummands().get(smd);
					if (singleton.getSort().getName() == "Real" || fac.abs() == Rational.ONE) {
						newLhs = singleton;
						linAdded.add(fac.negate(), smd);
						linAdded.mul(fac.negate().inverse());
						newRhs = linAdded.toTerm(lhs.getSort());
						break;
					}
				}
			}
		}
		final Term newTerm = mTheory.term("=", newLhs, newRhs);
		QuantLiteral atom = (QuantLiteral) mClausifier.getILiteral(newTerm);
		if (atom != null) {
			return atom;
		}
		addGroundCCTerms(newLhs, source);
		addGroundCCTerms(newRhs, source);
		atom = new QuantEquality(newLhs, newRhs);

		// Check if the atom is almost uninterpreted or can be used for DER.
		if (!(newLhs instanceof TermVariable)) { // (euEUTerm = euTerm) is essentially and almost uninterpreted
			if (QuantUtil.isEssentiallyUninterpreted(newLhs)
					&& QuantUtil.isEssentiallyUninterpreted(newRhs)) {
				atom.mIsEssentiallyUninterpreted = atom.negate().mIsEssentiallyUninterpreted = true;
			}
		} else if (!(newRhs instanceof TermVariable)) {
			// (x = t) for t integer is arithmetical and almost uninterpreted
			if (newRhs.getFreeVars().length == 0 && newRhs.getSort().getName() == "Int") {
				atom.mIsArithmetical = true;
			}
			// (x != termwithoutx) can be used for DER
			if (!Arrays.asList(newRhs.getFreeVars()).contains(newLhs)) {
				atom.negate().mIsDERUsable = true;
			}
		} else { // (var = var) is not almost uninterpreted, but the negated form can be used for DER
			atom.negate().mIsDERUsable = true;
		}
		mClausifier.setTermFlags(newTerm,
				mClausifier.getTermFlags(newTerm) | Clausifier.POS_AUX_AXIOMS_ADDED | Clausifier.NEG_AUX_AXIOMS_ADDED);
		mClausifier.setLiteral(newTerm, atom);
		return atom;
	}

	/**
	 * This method builds new QuantInequality literals and simultaneously checks if they lie in the almost uninterpreted
	 * fragment, i.e., if they are of the form (i) (eu <= 0), pos. and neg., (ii) (var < var), (iii) (var < ground), or
	 * (iv) (ground < var).
	 * <p>
	 * For integers x, positive (x-t<=0) are rewritten into ~(t+1<=x), or more precisely, ~(-x+t+1<=0). Note that this
	 * method can therefore return negated literals! For reals x, we normalize atoms (kx-t<= 0) to get (±x-t<=0).
	 * <p>
	 * TODO Offsets? (See paper)
	 *
	 * @param positive
	 *            should be true if the literal appears positively in the clause and false else
	 * @param lhs
	 *            the left side of the inequality (t <= 0)
	 * @return a QuantLiteral, possibly negated, of the form (t <= 0) or ~(t' <= 0)
	 */
	public QuantLiteral getQuantInequality(final boolean positive, final Term lhs, final SourceAnnotation source) {

		boolean rewrite = false; // Set to true when rewriting positive (x-t<=0) into ~(t+1<=x) for x integer
		final Polynomial linTerm = new Polynomial(lhs);
		TermVariable var = null;
		Rational fac = Rational.ONE;
		boolean hasUpperBound = false;
		for (final Map<Term, Integer> monom : linTerm.getSummands().keySet()) {
			if (monom.size() == 1 && monom.values().iterator().next() == 1) {
				final Term smd = monom.keySet().iterator().next();
				if (smd instanceof TermVariable) {
					fac = linTerm.getSummands().get(monom);
					if (smd.getSort().getName() == "Real") { // In the real case, we normalize the term for this var.
						var = (TermVariable) smd;
						if (fac.isNegative()) {
							hasUpperBound = true;
						} else {
							hasUpperBound = false;
						}
						break;
					} else {
						if (fac == Rational.MONE) {
							var = (TermVariable) smd;
							hasUpperBound = true;
							break;
						} else if (fac == Rational.ONE) {
							var = (TermVariable) smd;
							hasUpperBound = false;
							break;
						}
					}
				}

			}
		}
		if (positive && var != null && lhs.getSort().getName() == "Int") {
			// Rewrite positive (x-t<=0) into ~(t+1<=x), or more precisely, ~(-x+t+1<=0) for x integer.
			// Similarly (t-x<=0) into ~(x-t+1<=0)
			rewrite = true;
			linTerm.mul(Rational.MONE);
			linTerm.add(Rational.ONE);
			hasUpperBound = !hasUpperBound;
		} else if (var != null && lhs.getSort().getName() == "Real") {
			// var should have coefficient 1 or -1.
			linTerm.mul(fac.abs().inverse());
		}

		final TermCompiler compiler = mClausifier.getTermCompiler();
		final Term newLhs = linTerm.toTerm(lhs.getSort());
		final Term newAtomTerm = mTheory.term("<=", newLhs, Rational.ZERO.toTerm(lhs.getSort()));
		QuantLiteral atom = (QuantLiteral) mClausifier.getILiteral(newAtomTerm);
		if (atom != null) {
			return rewrite ? atom.negate() : atom;
		}
		atom = new QuantBoundConstraint(newAtomTerm, linTerm);
		addGroundCCTerms(newLhs, source);

		// Check if the atom is almost uninterpreted.
		if (var == null) { // (euTerm <= 0), pos. and neg., is essentially and almost uninterpreted.
			boolean hasOnlyEU = true;
			for (final Map<Term, Integer> monom : linTerm.getSummands().keySet()) {
				for (final Term smd : monom.keySet()) {
					hasOnlyEU = hasOnlyEU && QuantUtil.isEssentiallyUninterpreted(smd);
				}
			}
			if (hasOnlyEU) {
				atom.mIsEssentiallyUninterpreted = atom.negate().mIsEssentiallyUninterpreted = true;
			}
		} else { // (var < var), (var < ground), or (ground < var) are arithmetical and almost uninterpreted
			final Polynomial remainderAff = new Polynomial();
			remainderAff.add(Rational.ONE, linTerm);
			remainderAff.add(hasUpperBound ? Rational.ONE : Rational.MONE, var);
			if (!hasUpperBound) {
				remainderAff.mul(Rational.MONE);
			}
			final Term remainder = remainderAff.toTerm(lhs.getSort());
			if (remainder instanceof TermVariable || remainder.getFreeVars().length == 0) {
				atom.negate().mIsArithmetical = true;
			}
		}
		mClausifier.setTermFlags(newAtomTerm, mClausifier.getTermFlags(newAtomTerm) | Clausifier.POS_AUX_AXIOMS_ADDED
				| Clausifier.NEG_AUX_AXIOMS_ADDED);
		mClausifier.setLiteral(newAtomTerm, atom);
		return rewrite ? atom.negate() : atom;
	}

	/**
	 * Get copies for quantified literals that are uniquely assigned to a clause.
	 *
	 * @param lits
	 *            the quantified literals.
	 * @param clause
	 *            the quantified clause these literals occur in.
	 * @return copies of the quantified literals that know their clause.
	 */
	public QuantLiteral[] getLiteralCopies(final QuantLiteral[] lits, final QuantClause clause) {
		final QuantLiteral[] clauseLiterals = new QuantLiteral[lits.length];
		for (int i = 0; i < lits.length; i++) {
			final QuantLiteral atom = lits[i].getAtom();
			final QuantLiteral clauseAtom;
			if (atom instanceof QuantBoundConstraint) {
				clauseAtom = new QuantBoundConstraint(atom.getTerm(), ((QuantBoundConstraint) atom).getAffineTerm());
			} else if (atom instanceof QuantAuxEquality) {
				final QuantAuxEquality auxAtom = (QuantAuxEquality) atom;
				clauseAtom = new QuantAuxEquality(auxAtom.getLhs(), auxAtom.getRhs(), auxAtom.getDefinition());
			} else {
				clauseAtom = new QuantEquality(((QuantEquality) atom).getLhs(), ((QuantEquality) atom).getRhs());
			}
			clauseAtom.mClause = clause;
			clauseAtom.mIsEssentiallyUninterpreted = atom.mIsEssentiallyUninterpreted;
			clauseAtom.mIsArithmetical = atom.mIsArithmetical;
			clauseAtom.mIsDERUsable = atom.mIsDERUsable;
			clauseAtom.mNegated.mClause = clause;
			clauseAtom.mNegated.mIsEssentiallyUninterpreted = atom.mNegated.mIsEssentiallyUninterpreted;
			clauseAtom.mNegated.mIsArithmetical = atom.mNegated.mIsArithmetical;
			clauseAtom.mNegated.mIsDERUsable = atom.mNegated.mIsDERUsable;

			clauseLiterals[i] = lits[i].isNegated() ? clauseAtom.negate() : clauseAtom;
		}
		return clauseLiterals;
	}

	/**
	 * Perform destructive equality reasoning.
	 * @param vars       The quantified variables.
	 * @param groundLits The ground literals of the clause.
	 * @param quantLits  The quantified literals of the clause.
	 * @param source     The source of the clause.
	 *
	 * @return the result from performing DER if something has changed, null else.
	 */
	public DERResult performDestructiveEqualityReasoning(final TermVariable[] vars, final Literal[] groundLits,
			final QuantLiteral[] quantLits, final SourceAnnotation source) {
		final DestructiveEqualityReasoning der =
				new DestructiveEqualityReasoning(this, vars, groundLits, quantLits, source);
		if (der.applyDestructiveEqualityReasoning()) {
			final DERResult result = der.getResult();
			if (result.isGround() && !result.isTriviallyTrue()) {
				mLogger.debug("Quant: DER returned ground clause.");
				mNumInstancesDER++;
			}
			return result;
		} else {
			return null;
		}
	}

	/**
	 * Add a QuantClause for a given set of literals and quantified literals.
	 *
	 * Call this only after performing DER.
	 *
	 * @param vars            the variables of the quantified formula
	 * @param groundLits      the ground literals of the clause to add.
	 * @param quantLits       the quantified literals of the clause to add.
	 * @param source          the source of the clause
	 * @param clauseWithProof the clause term, possibly annotated with its proof
	 */
	public void addQuantClause(final TermVariable[] vars, final Literal[] groundLits, final QuantLiteral[] quantLits,
			final SourceAnnotation source, final Term clauseWithProof) {
		for (final QuantLiteral l : quantLits) {
			if (!l.isAlmostUninterpreted()) {
				mLogger.info("Quant: Clause contains literal that is not almost uninterpreted: %s", l);
			} else if (l.mIsDERUsable) {
				mLogger.warn("Quant: Clause contains disequality on variable not eliminated by DER: %s", l);
			}
		}
		if (quantLits.length == 0) {
			throw new IllegalArgumentException("Cannot add clause to QuantifierTheory: No quantified literal!");
		}

		final QuantClause clause = new QuantClause(vars, groundLits, quantLits, this, source, clauseWithProof);
		mQuantClauses.add(clause);

		mEMatching.addClause(clause);
		mInstantiationManager.addClause(clause);

		if (clause.hasArrayIndices()) {
			mClausifier.getArrayTheory().setNeedDiffIndices();
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Quant: Added clause: " + clause);
		}
	}

	public void addEMatchingTime(final long time) {
		mEMatchingTime += time;
	}

	public void addDawgTime(final long time) {
		mDawgTime += time;
	}

	public Clausifier getClausifier() {
		return mClausifier;
	}

	public CClosure getCClosure() {
		return mCClosure;
	}

	public EMatching getEMatching() {
		return mEMatching;
	}

	public DPLLEngine getEngine() {
		return mEngine;
	}

	public LinArSolve getLinAr() {
		return mLinArSolve;
	}

	public InstantiationManager getInstantiationManager() {
		return mInstantiationManager;
	}

	public LogProxy getLogger() {
		return mLogger;
	}

	public Collection<QuantClause> getQuantClauses() {
		return mQuantClauses;
	}

	public Theory getTheory() {
		return mTheory;
	}

	public InstantiationMethod getInstantiationMethod() {
		return mInstantiationMethod;
	}

	protected Term getLambda(final Sort sort) {
		if (mLambdas.containsKey(sort)) {
			return mLambdas.get(sort);
		}
		Term lambda;
		if (sort.getName().equals("Bool")) {
			lambda = mTheory.mTrue;
		} else {
			final FunctionSymbol fsym = mTheory.getFunctionWithResult("@0", null, sort, new Sort[0]);
			lambda = mTheory.term(fsym);
		}
		mLambdas.put(sort, lambda);
		return lambda;
	}

	/**
	 * Check if there exists a not yet satisfied clause that contains a literal outside of the almost uninterpreted
	 * fragment. If so, returns INCOMPLETE to inform the DPLL engine of incompleteness.
	 *
	 * @return DPLLEngine.COMPLETE, if a model exists, DPLLEngine.INCOMPLETE_* if unsure.
	 */
	@Override
	public int checkCompleteness() {
		for (final QuantClause qClause : mQuantClauses) {
			if (!qClause.hasTrueGroundLits()) {
				for (final QuantLiteral qLit : qClause.getQuantLits()) {
					if (!qLit.isAlmostUninterpreted()) {
						return DPLLEngine.INCOMPLETE_QUANTIFIER;
					}
				}
				for (final Term lambda : mLambdas.values()) {
					if (!lambda.getSort().isNumericSort()) {
						final CCTerm lambdaCC = mClausifier.getCCTerm(lambda);
						if (lambdaCC != null && lambdaCC.getNumMembers() > 1) {
							return DPLLEngine.INCOMPLETE_QUANTIFIER;
						}
					}
				}
			}
		}
		return DPLLEngine.COMPLETE;
	}

	/**
	 * Add InstClauses to the internal map that manages which instances to add as clause to the DPLL engine. Each
	 * undecided literal in an InstClause is used as a key, and maps to the InstClauses it is contained in. This method
	 * also counts the number of undecided literals in an InstClause, makes sure not to add currently satisfied
	 * instances to the map, and if it finds a conflict in the given InstClauses, returns it as an actual Clause.
	 *
	 * @param instances
	 *            the InstClauses to add.
	 * @return a conflict, if it exists.
	 */
	private Clause addInstClausesToPending(final Collection<InstClause> instances) {
		if (instances == null) {
			return null;
		}
		for (final InstClause inst : instances) {
			if (mEngine.isTerminationRequested()) {
				return null;
			}
			final int numUndefLits = inst.countAndSetUndefLits();
			if (numUndefLits == -1) { // Instance is true.
				continue;
			}
			if (numUndefLits == 0) {
				return inst.toClause(mEngine.isProofGenerationEnabled());
			}
			for (final Literal lit : inst.mLits) {
				if (lit.getAtom().getDecideStatus() == null) {
					if (!mPendingInstances.containsKey(lit)) {
						mPendingInstances.put(lit, new LinkedHashSet<>());
					}
					mPendingInstances.get(lit).add(inst);
				}
			}
		}
		return null;
	}

	/**
	 * Get the term that is the current CC representative of the given term, if such term exists.
	 *
	 * @param term
	 *            a term.
	 * @return the the term corresponding to the current CC representative of the given term, if it exists, the input
	 *         term else.
	 */
	Term getRepresentativeTerm(final Term term) {
		final CCTerm ccTerm = getClausifier().getCCTerm(term);
		return ccTerm == null ? term : ccTerm.getRepresentative().getFlatTerm();
	}

	private void addGroundCCTerms(final Term term, final SourceAnnotation source) {
		final HashSet<Term> seen = new HashSet<>();
		final Deque<Term> todo = new ArrayDeque<>();
		todo.add(term);
		while (!todo.isEmpty()) {
			final Term subTerm = todo.pop();
			if (subTerm instanceof ApplicationTerm && seen.add(subTerm)) {
				if (subTerm.getFreeVars().length == 0) {
					final CCTerm ccTerm = mClausifier.getCCTerm(subTerm);
					if (ccTerm == null && (Clausifier.needCCTerm(subTerm) || subTerm.getSort().isArraySort())) {
						mClausifier.createCCTerm(subTerm, source);
					}
				} else {
					for (final Term arg : ((ApplicationTerm) subTerm).getParameters()) {
						todo.add(arg);
					}
				}
			}
		}
	}

	/**
	 * The origin of an instance of a quantified clause.
	 */
	public enum InstanceOrigin {
		CONFLICT(":conflict"), EMATCHING(":e-matching"), ENUMERATION(":enumeration");
		String mOrigin;

		private InstanceOrigin(final String origin) {
			mOrigin = origin;
		}

		/**
		 * Get the name of the instance origin. This can be used in an annotation for the lemma.
		 */
		public String getOrigin() {
			return mOrigin;
		}
	}

	/**
	 * Different instantiation methods for quantified formulae.
	 */
	public static enum InstantiationMethod {
		/**
		 * In checkpoint, build potential conflict and unit instances found by checking the substitutions determined by
		 * the almost uninterpreted fragment.
		 */
		AUF_CONFLICT,
		/**
		 * In checkpoint, build potential conflict and unit instances found by E-matching.
		 */
		E_MATCHING_CONFLICT,
		/**
		 * In checkpoint, build instances found by E-matching (don't build terms without equivalent known term).
		 */
		E_MATCHING_EAGER,
		/**
		 * In final check, build instances found by E-matching (don't build terms without equivalent known term).
		 */
		E_MATCHING_LAZY,
		/**
		 * In final check, build potential conflict and unit instances found by E-matching.
		 */
		E_MATCHING_CONFLICT_LAZY;
	}
}
