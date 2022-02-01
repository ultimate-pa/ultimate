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
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
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
	private final SourceAnnotation mQuantSource;
	private final Term mClauseWithProof;

	/**
	 * The quantified variables in this clause. Defines an order on the variables.
	 */
	private final TermVariable[] mVars;
	/**
	 * For each variable, the information needed for instantiation.
	 */
	private final VarInfo[] mVarInfos;
	/**
	 * For each variable, the set of potentially interesting substitutions for instantiation. The key stores the Term of
	 * the CC representative in case the value term has a CCTerm.
	 */
	private final LinkedHashMap<Term, Term>[] mInterestingTermsForVars;

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
	 * @param source
	 *            the SourceAnnotation for the clause.
	 * @param clauseWithProof
	 *            the clause term, potentially annotated with its proof.
	 */
	@SuppressWarnings("unchecked")
	QuantClause(final Literal[] groundLits, final QuantLiteral[] quantLits, final QuantifierTheory quantTheory,
			final SourceAnnotation source, final Term clauseWithProof) {
		assert quantLits.length != 0;
		mQuantTheory = quantTheory;

		mGroundLits = groundLits;
		mQuantLits = mQuantTheory.getLiteralCopies(quantLits, this);
		mSource = source;
		mQuantSource = new SourceAnnotation(source, true);
		mClauseWithProof = clauseWithProof;

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
	}

	/**
	 * Update the interesting instantiation terms for all variables.
	 */
	public void updateInterestingTermsAllVars() {
		for (int i = 0; i < mVars.length; i++) {
			collectBoundAndDefaultTerms(i);
			if (mVars[i].getSort().getName() != "Bool") {
				updateInterestingTermsForFuncArgs(mVars[i], i);
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

	/**
	 * Get the source annotation of this QuantClause. This should only be used when dealing with ground terms existing
	 * in the QuantClause.
	 * 
	 * @return the (ground) source annotation.
	 */
	public SourceAnnotation getSource() {
		return mSource;
	}

	/**
	 * Get the source annotation of this QuantClause containing the information that it comes from the QuantifierTheory.
	 * 
	 * @return the (quant) source annotation.
	 */
	public SourceAnnotation getQuantSource() {
		return mQuantSource;
	}

	public TermVariable[] getVars() {
		return mVars;
	}

	/**
	 * Get the ground terms that are compared with the given variable in an arithmetical literal.
	 *
	 * @param var
	 *            the variable.
	 * @return the ground bound terms (both upper and lower) for the given variable.
	 */
	public Set<Term> getGroundBounds(final TermVariable var) {
		final Set<Term> bounds = new LinkedHashSet<>();
		bounds.addAll(mVarInfos[getVarIndex(var)].mUpperGroundBounds);
		bounds.addAll(mVarInfos[getVarIndex(var)].mLowerGroundBounds);
		return bounds;
	}

	/**
	 * Get the variable terms that are compared with the given variable in an arithmetical literal.
	 *
	 * @param var
	 *            the variable.
	 * @return the variable bound terms (both upper and lower) for the given variable.
	 */
	public Set<TermVariable> getVarBounds(final TermVariable var) {
		final Set<TermVariable> bounds = new LinkedHashSet<>();
		bounds.addAll(mVarInfos[getVarIndex(var)].mUpperVarBounds);
		bounds.addAll(mVarInfos[getVarIndex(var)].mLowerVarBounds);
		return bounds;
	}

	/**
	 * Get the interesting terms for instantiation for all variables. This should only be called after updating the
	 * interesting terms.
	 *
	 * @return the interesting substitution terms for all variables.
	 */
	public LinkedHashMap<Term, Term>[] getInterestingTerms() {
		return mInterestingTermsForVars;
	}

	@Override
	public String toString() {
		return Arrays.toString(mGroundLits).concat(Arrays.toString(mQuantLits));
	}

	public Term toTerm(final Theory theory) {
		final int groundLength = mGroundLits.length;
		final int quantLength = mQuantLits.length;
		final Term[] litTerms = new Term[groundLength + quantLength];
		for (int i = 0; i < groundLength; i++) {
			litTerms[i] = mGroundLits[i].getSMTFormula(theory);
		}
		for (int i = 0; i < quantLength; i++) {
			litTerms[i + groundLength] = mQuantLits[i].getTerm();
		}
		return theory.or(litTerms);
	}

	/**
	 * Get the clause term potentially annotated with its proof.
	 */
	public Term getClauseWithProof() {
		return mClauseWithProof;
	}

	void clearInterestingTerms() {
		for (int i = 0; i < mVars.length; i++) {
			mInterestingTermsForVars[i].clear();
		}
	}

	/**
	 * Compute the free variables in this clause. This defines an order on the variables in the clause.
	 *
	 * @return an array containing the free variables in this clause.
	 */
	private TermVariable[] computeVars() {
		final Set<TermVariable> varSet = new LinkedHashSet<>();
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
	 * @return the position of var, if contained in this clause, -1 else.
	 */
	int getVarIndex(final TermVariable var) {
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
									varInfo.addUpperGroundBound(remainderTerm);
								} else {
									varInfo.addLowerGroundBound(remainderTerm);
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
							varInfo.addLowerGroundBound(lowerBound);
							varInfo.addUpperGroundBound(upperBound);
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
	 *
	 * @param qTerm
	 *            a function application.
	 */
	private void addAllVarPos(final ApplicationTerm qTerm) {
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
	 * Collects the lower and upper bound and the default terms for a variable for instantiation.
	 *
	 * @param varPos
	 *            the position of the variable.
	 */
	private void collectBoundAndDefaultTerms(final int varPos) {
		addAllInteresting(mInterestingTermsForVars[varPos], mVarInfos[varPos].mLowerGroundBounds);
		addAllInteresting(mInterestingTermsForVars[varPos], mVarInfos[varPos].mUpperGroundBounds);
		if (mVars[varPos].getSort().getName() == "Bool") {
			final Term sharedTrue = mQuantTheory.getTheory().mTrue;
			final Term sharedFalse = mQuantTheory.getTheory().mFalse;
			mInterestingTermsForVars[varPos].put(sharedTrue, sharedTrue);
			mInterestingTermsForVars[varPos].put(sharedFalse, sharedFalse);
		} else {
			final Term lambda = mQuantTheory.getLambda(mVars[varPos].getSort());
			mInterestingTermsForVars[varPos].put(lambda, lambda);
		}
	}

	/**
	 * If two variables depend on each other, synchronize their instantiation sets.
	 */
	private void synchronizeInterestingTermsAllVars() {
		boolean changed = true;
		while (changed && !mQuantTheory.getEngine().isTerminationRequested()) {
			changed = false;
			for (int i = 0; i < mVars.length; i++) {
				for (final TermVariable t : getVarBounds(mVars[i])) {
					final int j = getVarIndex(t);
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
	private void updateInterestingTermsForFuncArgs(final TermVariable var, final int varNum) {
		final VarInfo info = mVarInfos[getVarIndex(var)];
		assert info != null;

		// Retrieve from CClosure all ground terms that appear under the same functions at the same positions as var
		final Set<Term> interestingTerms = new LinkedHashSet<>();
		for (final Entry<FunctionSymbol, BitSet> entry : info.mFuncArgPositions.entrySet()) {
			if (mQuantTheory.getEngine().isTerminationRequested()) {
				return;
			}
			final FunctionSymbol func = entry.getKey();
			final BitSet pos = entry.getValue();
			for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
				final Collection<CCTerm> argTerms = mQuantTheory.mCClosure.getArgTermsForFunc(func, i);
				if (argTerms != null) {
					for (final CCTerm ccTerm : argTerms) {
						interestingTerms.add(ccTerm.getFlatTerm());
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
							final Term idxTerm = idx.getFlatTerm();
							final SMTAffineTerm idxPlusMinusOneAff = new SMTAffineTerm(idxTerm);
							idxPlusMinusOneAff.add(offset);
							final Term shared = idxPlusMinusOneAff.toTerm(idxTerm.getSort());
							interestingTerms.add(shared);
						}
					}
				}
			} // TODO: maybe for store(a,x,v) we need all i in select(b,i)
		}
		addAllInteresting(mInterestingTermsForVars[varNum], interestingTerms);
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
	private boolean addAllInteresting(final Map<Term, Term> interestingTerms, final Collection<Term> newTerms) {
		boolean changed = false;
		for (final Term newTerm : newTerms) {
			final Term rep = mQuantTheory.getRepresentativeTerm(newTerm);
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
		private final Map<FunctionSymbol, BitSet> mFuncArgPositions;
		// TODO Do we need both lower and upper bounds?
		private final Set<Term> mLowerGroundBounds;
		private final Set<Term> mUpperGroundBounds;
		private final Set<TermVariable> mLowerVarBounds;
		private final Set<TermVariable> mUpperVarBounds;

		/**
		 * Create a new VarInfo. This is used to store information for one variable: - lower and upper ground and
		 * variable bounds and - functions and positions where the variable appears as argument.
		 */
		VarInfo() {
			mFuncArgPositions = new LinkedHashMap<>();
			mLowerGroundBounds = new LinkedHashSet<>();
			mUpperGroundBounds = new LinkedHashSet<>();
			mLowerVarBounds = new LinkedHashSet<>();
			mUpperVarBounds = new LinkedHashSet<>();
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
				final BitSet occs = mFuncArgPositions.get(func);
				occs.set(pos);
			} else {
				final BitSet occs = new BitSet(func.getParameterSorts().length);
				occs.set(pos);
				mFuncArgPositions.put(func, occs);
			}
		}

		void addLowerGroundBound(final Term lowerBound) {
			mLowerGroundBounds.add(lowerBound);
		}

		void addUpperGroundBound(final Term upperBound) {
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
