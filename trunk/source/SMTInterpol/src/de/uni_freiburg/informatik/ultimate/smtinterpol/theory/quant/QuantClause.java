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

import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

/**
 * Represents a clause in the QuantifierTheory. This means, it contains at least one literal with an (implicitly)
 * universally quantified variable.
 *
 * @author Tanja Schindler
 */
public class QuantClause {

	private final QuantifierTheory mQuantTheory;
	private final Literal[] mGroundLits;
	private final QuantLiteral[] mQuantLits;

	private final SourceAnnotation mSource;

	/**
	 * The quantified variables in this clause. Defines an order on the variables.
	 */
	private final TermVariable[] mVars;
	/**
	 * For each variable, the information needed for instantiation.
	 */
	private final VarInfo[] mVarInfos;
	/**
	 * For each variable, the set of potentially interesting instantiations. The key stores the SharedTerm of the
	 * representative in case the value term has a CCTerm.
	 */
	private final LinkedHashMap<SharedTerm, SharedTerm>[] mInterestingTermsForVars;

	/**
	 * Build a new QuantClause. At least one literal must not be ground. This should only be called after performing
	 * DER. This also builds copies of the quantified literals that know their clause.
	 *
	 * @param groundLits
	 *            the ground literals in this clause.
	 * @param quantLits
	 *            the quantified literals in this clause. This must not be empty.
	 * @param quantTheory
	 *            the QuantifierTheory.
	 */
	@SuppressWarnings("unchecked")
	QuantClause(final Literal[] groundLits, final QuantLiteral[] quantLits, final QuantifierTheory quantTheory,
			final SourceAnnotation source) {
		assert quantLits.length != 0;
		mQuantTheory = quantTheory;

		mGroundLits = groundLits;
		mQuantLits = mQuantTheory.getLiteralCopies(quantLits, this);
		mSource = source;

		mVars = computeVars();
		mVarInfos = new VarInfo[mVars.length];
		for (int i = 0; i < mVars.length; i++) {
			mVarInfos[i] = new VarInfo();
		}
		
		collectVarInfos();
		mInterestingTermsForVars = new LinkedHashMap[mVars.length];
		for (int i = 0; i < mVars.length; i++) {
			mInterestingTermsForVars[i] = new LinkedHashMap<>();
		}
		collectInitialInterestingTermsAllVars();
	}

	/**
	 * Update the interesting instantiation terms for all variable with terms from CClosure.
	 */
	public void updateInterestingTermsAllVars() {
		for (int i = 0; i < mVars.length; i++) {
			if (mVars[i].getSort().getName() != "Bool") {
				updateInterestingTermsOneVar(mVars[i], i);
			}
		}
		synchronizeInterestingTermsAllVars();
	}

	/**
	 * Check if some of the ground literals in this clause is currently set to true.
	 */
	public boolean hasTrueGroundLits() {
		for (final Literal lit : mGroundLits) {
			if (lit.getAtom().getDecideStatus() == lit) {
				return true;
			}
		}
		return false;
	}

	public QuantifierTheory getQuantTheory() {
		return mQuantTheory;
	}

	public Literal[] getGroundLits() {
		return mGroundLits;
	}

	public QuantLiteral[] getQuantLits() {
		return mQuantLits;
	}

	public SourceAnnotation getSource() {
		return mSource;
	}

	public TermVariable[] getVars() {
		return mVars;
	}

	public Set<SharedTerm> getGroundBounds(final TermVariable var) {
		final Set<SharedTerm> bounds = new LinkedHashSet<>();
		bounds.addAll(mVarInfos[getVarIndex(var)].mUpperGroundBounds);
		bounds.addAll(mVarInfos[getVarIndex(var)].mLowerGroundBounds);
		return bounds;
	}

	public Set<TermVariable> getVarBounds(final TermVariable var) {
		final Set<TermVariable> bounds = new LinkedHashSet<>();
		bounds.addAll(mVarInfos[getVarIndex(var)].mUpperVarBounds);
		bounds.addAll(mVarInfos[getVarIndex(var)].mLowerVarBounds);
		return bounds;
	}

	public LinkedHashMap<SharedTerm, SharedTerm>[] getInterestingTerms() {
		return mInterestingTermsForVars;
	}

	@Override
	public String toString() {
		return Arrays.toString(mGroundLits).concat(Arrays.toString(mQuantLits));
	}

	/**
	 * Compute the free variables in this clause.
	 *
	 * @return an array containing the free variables in this clause.
	 */
	private TermVariable[] computeVars() {
		final Set<TermVariable> varSet = new LinkedHashSet<TermVariable>();
		for (final QuantLiteral lit : mQuantLits) {
			final TermVariable[] vars = lit.getTerm().getFreeVars();
			Collections.addAll(varSet, vars);
		}
		return varSet.toArray(new TermVariable[varSet.size()]);
	}

	/**
	 * Get the position of a given variable.
	 * 
	 * @param var
	 *            a TermVariable
	 * @return the position of var, if contained in this clause.
	 */
	int getVarIndex(TermVariable var) {
		return Arrays.asList(mVars).indexOf(var);
	}

	/**
	 * Go through the quantified literals in this clause to collect information about the appearing variables. In
	 * particular, for each variable we collect the lower and upper ground bounds and variable bounds, and the functions
	 * and positions where the variable appears as argument.
	 * 
	 * TODO What about offsets? (See paper)
	 */
	private void collectVarInfos() {
		for (final QuantLiteral lit : mQuantLits) {
			final QuantLiteral atom = lit.getAtom();
			final boolean isNegated = lit.isNegated();

			if (atom instanceof QuantBoundConstraint) {
				final QuantBoundConstraint constr = (QuantBoundConstraint) atom;
				final SMTAffineTerm lhs = constr.getAffineTerm();
				for (final Term smd : lhs.getSummands().keySet()) {
					if (smd instanceof TermVariable) {
						final Rational fac = lhs.getSummands().get(smd);
						if (fac.abs() == Rational.ONE) {
							final SMTAffineTerm remainder = new SMTAffineTerm();
							remainder.add(lhs);
							remainder.add(fac.negate(), smd);
							if (!fac.isNegative()) {
								remainder.mul(Rational.MONE);
							}
							final Term remainderTerm = remainder.toTerm(smd.getSort());
							if (remainderTerm.getFreeVars().length == 0) {
								final int pos = getVarIndex((TermVariable) smd);
								final VarInfo varInfo = mVarInfos[pos];
								if (fac.isNegative()) {
									varInfo.addUpperGroundBound(
											mQuantTheory.getClausifier().getSharedTerm(remainderTerm,
													mSource));
								} else {
									varInfo.addLowerGroundBound(mQuantTheory.getClausifier()
											.getSharedTerm(remainderTerm, mSource));
								}
							} else if (remainderTerm instanceof TermVariable) {
								final int pos = getVarIndex((TermVariable) smd);
								final VarInfo varInfo = mVarInfos[pos];
								if (fac.isNegative()) {
									varInfo.addUpperVarBound((TermVariable) remainderTerm);
								} else {
									varInfo.addLowerVarBound((TermVariable) remainderTerm);
								}
							}
						}
					} else if (smd.getFreeVars().length != 0) {
						assert smd instanceof ApplicationTerm;
						addAllVarPos((ApplicationTerm) smd);
					}
				}
			} else {
				assert atom instanceof QuantEquality;
				final QuantEquality eq = (QuantEquality) atom;
				final Term lhs = eq.getLhs();
				final Term rhs = eq.getRhs();
				if (lhs instanceof TermVariable) {
					if (lhs.getSort().getName() == "Int" && !isNegated) {
						if (rhs.getFreeVars().length == 0) { // (x = t) -> add t-1, t+1
							final int pos = getVarIndex((TermVariable) lhs);
							final VarInfo varInfo = mVarInfos[pos];
							final SMTAffineTerm lowerAffine = new SMTAffineTerm(rhs);
							lowerAffine.add(Rational.MONE);
							final SMTAffineTerm upperAffine = new SMTAffineTerm(rhs);
							upperAffine.add(Rational.ONE);
							final Term lowerBound = lowerAffine.toTerm(rhs.getSort());
							final Term upperBound = upperAffine.toTerm(rhs.getSort());
							varInfo.addLowerGroundBound(
									mQuantTheory.getClausifier().getSharedTerm(lowerBound, mSource));
							varInfo.addUpperGroundBound(
									mQuantTheory.getClausifier().getSharedTerm(upperBound, mSource));
						}
					}
				}
				else if (lhs.getFreeVars().length != 0) {
					assert lhs instanceof ApplicationTerm;
					addAllVarPos((ApplicationTerm) lhs);
				}
				if (!(rhs instanceof TermVariable) && rhs.getFreeVars().length != 0) {
					assert rhs instanceof ApplicationTerm;
					addAllVarPos((ApplicationTerm) rhs);
				}
			}
		}
	}

	/**
	 * For each variable in the given term, add the functions and positions where it appears as argument to the VarInfo.
	 */
	private void addAllVarPos(ApplicationTerm qTerm) {
		final FunctionSymbol func = qTerm.getFunction();
		final Term[] args = qTerm.getParameters();
		if (!func.isInterpreted() || func.getName() == "select") {
			for (int i = 0; i < args.length; i++) {
				final Term arg = args[i];
				if (arg instanceof TermVariable) {
					final int index = getVarIndex((TermVariable) arg);
					final VarInfo varInfo = mVarInfos[index];
					varInfo.addPosition(func, i);
				} else if (arg.getFreeVars().length != 0) {
					assert arg instanceof ApplicationTerm;
					addAllVarPos((ApplicationTerm) arg);
				}
			}
		} else if (func.getName() == "+" || func.getName() == "-" || func.getName() == "*") {
			final SMTAffineTerm affine = new SMTAffineTerm(qTerm);
			for (final Term smd : affine.getSummands().keySet()) {
				if (smd instanceof ApplicationTerm) {
					addAllVarPos((ApplicationTerm) smd);
				}
			}
		}
	}

	/**
	 * Collects the lower and upper bound terms for variables for instantiation.
	 *
	 * Synchronizes the sets of variables that are bounds of each other.
	 */
	private void collectInitialInterestingTermsAllVars() {
		for (int i = 0; i < mVars.length; i++) {
			addAllInteresting(mInterestingTermsForVars[i], mVarInfos[i].mLowerGroundBounds);
			addAllInteresting(mInterestingTermsForVars[i], mVarInfos[i].mUpperGroundBounds);
			if (mVars[i].getSort().getName() == "Bool") {
				final SharedTerm sharedTrue =
						mQuantTheory.getClausifier().getSharedTerm(mQuantTheory.getTheory().mTrue, mSource);
				final SharedTerm sharedFalse =
						mQuantTheory.getClausifier().getSharedTerm(mQuantTheory.getTheory().mFalse, mSource);
				mInterestingTermsForVars[i].put(sharedTrue, sharedTrue);
				mInterestingTermsForVars[i].put(sharedFalse, sharedFalse);
			} else {
				final SharedTerm lambda = mQuantTheory.getLambda(mVars[i].getSort());
				mInterestingTermsForVars[i].put(lambda, lambda);
			}
		}
		synchronizeInterestingTermsAllVars();
	}

	/**
	 * If two variables depend on each other, synchronize their instantiation sets.
	 */
	private void synchronizeInterestingTermsAllVars() {
		boolean changed = true;
		while (changed) {
			changed = false;
			for (int i = 0; i < mVars.length; i++) {
				for (TermVariable t : getVarBounds(mVars[i])) {
					int j = getVarIndex(t);
					changed = addAllInteresting(mInterestingTermsForVars[i], mInterestingTermsForVars[j].values());
				}
			}
		}
	}

	/**
	 * Update the interesting instantiation terms for a given variable, using the terms in CClosure.
	 * <p>
	 * This method does not consider dependencies between variables. They must be taken care of after computing the sets
	 * for each single variable.
	 *
	 * @param var
	 *            the TermVariable which we compute the instantiation terms for.
	 * @param varNum
	 *            the number of the variable
	 */
	private void updateInterestingTermsOneVar(final TermVariable var, final int varNum) {
		final VarInfo info = mVarInfos[getVarIndex(var)];
		assert info != null;

		// Retrieve from CClosure all ground terms that appear under the same functions at the same positions as var
		for (final Entry<FunctionSymbol, BitSet> entry : info.mFuncArgPositions.entrySet()) {
			final FunctionSymbol func = entry.getKey();
			final BitSet pos = entry.getValue();
			for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
				final Collection<CCTerm> argTerms = mQuantTheory.mCClosure.getArgTermsForFunc(func, i);
				if (argTerms != null) {
					for (final CCTerm ccTerm : argTerms) {
						final SharedTerm repShared, ccShared;
						if (ccTerm.getRepresentative().getSharedTerm() != null) {
							repShared = ccTerm.getRepresentative().getSharedTerm();
						} else {
							repShared = ccTerm.getRepresentative().getFlatTerm();
						}
						if (ccTerm.getSharedTerm() != null) {
							ccShared = ccTerm.getSharedTerm();
						} else {
							ccShared = ccTerm.getFlatTerm();
						}
						mInterestingTermsForVars[varNum].put(repShared, ccShared);
					}
				}
			}
			if (pos.get(1) && func.getName() == "select" && var.getSort().getName() == "Int") {
				// Add all store indices +-1.
				final Sort[] storeSorts = new Sort[3];
				storeSorts[0] = func.getParameterSorts()[0];
				storeSorts[1] = func.getParameterSorts()[1];
				storeSorts[2] = func.getReturnSort();
				final FunctionSymbol store = mQuantTheory.getTheory().getFunction("store", storeSorts);
				final Collection<CCTerm> storeIndices = mQuantTheory.mCClosure.getArgTermsForFunc(store, 1);
				if (storeIndices != null) {
					for (final CCTerm idx : storeIndices) {
						for (final Rational offset : new Rational[] { Rational.ONE, Rational.MONE }) {
							final SMTAffineTerm idxPlusMinusOneAff = new SMTAffineTerm(idx.getSharedTerm().getTerm());
							idxPlusMinusOneAff.add(offset);
							final SharedTerm shared = mQuantTheory.getClausifier()
									.getSharedTerm(idxPlusMinusOneAff.toTerm(idx.getSharedTerm().getSort()),
											mSource);
							SharedTerm repShared = shared;
							final CCTerm cc = shared.getCCTerm();
							if (cc != null) {
								final SharedTerm ccRepShared = cc.getRepresentative().getSharedTerm();
								if (ccRepShared != null) {
									repShared = ccRepShared;
								} else if (cc.getSharedTerm() != null) {
									repShared = cc.getSharedTerm();
								}
							}
							mInterestingTermsForVars[varNum].put(repShared, shared);
						}
					}
				}
			} // TODO: maybe for store(a,x,v) we need all i in select(b,i)
		}
	}

	/**
	 * Helper method to add interesting instantiation terms without adding equivalent terms more than once.
	 *
	 * If there exists a CCTerm, we use the SharedTerm of the representative as key, otherwise, just the SharedTerm
	 * itself.
	 *
	 * @param interestingTerms
	 *            The interesting instantiationTerms, with the representative as key (if it exists).
	 * @param newTerms
	 *            The interesting terms that should be added, if no equivalent term is in the map yet.
	 * @return true if new terms were added, false otherwise.
	 */
	private boolean addAllInteresting(Map<SharedTerm, SharedTerm> interestingTerms, Collection<SharedTerm> newTerms) {
		boolean changed = false;
		for (SharedTerm newTerm : newTerms) {
			SharedTerm rep = newTerm;
			if (newTerm.getCCTerm() != null) {
				rep = newTerm.getCCTerm().getRepresentative().getFlatTerm();
			}
			if (!interestingTerms.containsKey(rep)) {
				interestingTerms.put(rep, newTerm);
				changed = true;
			}
		}
		return changed;
	}

	/**
	 * Contains information for variable instantiation, i.e. the functions where the variable is an argument and this
	 * argument's position, and the lower and upper bounds for the variable.
	 */
	private class VarInfo {
		private Map<FunctionSymbol, BitSet> mFuncArgPositions;
		// TODO Do we need both lower and upper bounds?
		private Set<SharedTerm> mLowerGroundBounds;
		private Set<SharedTerm> mUpperGroundBounds;
		private Set<TermVariable> mLowerVarBounds;
		private Set<TermVariable> mUpperVarBounds;

		/**
		 * Create a new VarInfo. This is used to store information for one variable: - lower and upper ground bounds and
		 * - functions and positions where the variable appears as argument.
		 */
		VarInfo() {
			mFuncArgPositions = new LinkedHashMap<FunctionSymbol, BitSet>();
			mLowerGroundBounds = new LinkedHashSet<SharedTerm>();
			mUpperGroundBounds = new LinkedHashSet<SharedTerm>();
			mLowerVarBounds = new LinkedHashSet<TermVariable>();
			mUpperVarBounds = new LinkedHashSet<TermVariable>();
		}

		/**
		 * Add a position where the variable appears as function argument.
		 *
		 * @param func
		 *            the function under which the variable appears as argument.
		 * @param pos
		 *            the position of this argument.
		 */
		void addPosition(final FunctionSymbol func, final int pos) {
			if (mFuncArgPositions.containsKey(func)) {
				BitSet occs = mFuncArgPositions.get(func);
				occs.set(pos);
			} else {
				BitSet occs = new BitSet(func.getParameterSorts().length);
				occs.set(pos);
				mFuncArgPositions.put(func, occs);
			}
		}

		void addLowerGroundBound(final SharedTerm lowerBound) {
			mLowerGroundBounds.add(lowerBound);
		}

		void addUpperGroundBound(final SharedTerm upperBound) {
			mUpperGroundBounds.add(upperBound);
		}

		void addLowerVarBound(final TermVariable lower) {
			mLowerVarBounds.add(lower);
		}

		void addUpperVarBound(final TermVariable lower) {
			mUpperVarBounds.add(lower);
		}
	}
}
