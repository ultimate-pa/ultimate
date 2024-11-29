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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

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
	QuantClause(final TermVariable[] vars, final Literal[] groundLits, final QuantLiteral[] quantLits,
			final QuantifierTheory quantTheory,
			final SourceAnnotation source, final Term clauseWithProof) {
		assert quantLits.length != 0;
		mQuantTheory = quantTheory;

		mGroundLits = groundLits;
		mQuantLits = mQuantTheory.getLiteralCopies(quantLits, this);
		mSource = source;
		mQuantSource = new SourceAnnotation(source, true);
		mClauseWithProof = clauseWithProof;

		mVars = vars;
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
	 * Get the position of a given variable.
	 *
	 * @param var
	 *            a TermVariable
	 * @return the position of var, if contained in this clause, -1 else.
	 */
	int getVarIndex(final TermVariable var) {
		return Arrays.asList(mVars).indexOf(var);
	}

	public boolean hasArrayIndices() {
		for (int i = 0; i < mVars.length; i++) {
			for (final ApplicationTerm term : mVarInfos[i].mArrayTermsWithVar) {
				if (term.getParameters()[1] == mVars[i]) {
					return true;
				}
			}
		}
		return false;
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
			if (atom instanceof QuantBoundConstraint) {
				if (lit.isArithmetical()) {
					final Term[] termLtTerm =
							QuantUtil.getArithmeticalTermLtTerm(lit, mQuantTheory.getClausifier().getTermCompiler());
					if (termLtTerm[0] instanceof TermVariable) {
						final TermVariable lowerVar = (TermVariable) termLtTerm[0];
						final VarInfo info = mVarInfos[getVarIndex(lowerVar)];
						if (termLtTerm[1] instanceof TermVariable) {
							info.addUpperVarBound((TermVariable) termLtTerm[1]);
						} else {
							assert termLtTerm[1].getFreeVars().length == 0;
							info.addUpperGroundBound(termLtTerm[1]);
						}
					}
					if (termLtTerm[1] instanceof TermVariable) {
						final TermVariable upperVar = (TermVariable) termLtTerm[1];
						final VarInfo info = mVarInfos[getVarIndex(upperVar)];
						if (termLtTerm[0] instanceof TermVariable) {
							info.addLowerVarBound((TermVariable) termLtTerm[0]);
						} else {
							assert termLtTerm[0].getFreeVars().length == 0;
							info.addLowerGroundBound(termLtTerm[0]);
						}
					}
				} else {
					for (final Map<Term, Integer> monom : ((QuantBoundConstraint) atom).getAffineTerm().getSummands()
							.keySet()) {
						for (final Term factor : monom.keySet()) {
							if (factor instanceof ApplicationTerm && factor.getFreeVars().length != 0) {
								addVarArgInfo((ApplicationTerm) factor);
							}
						}
					}
				}
			} else {
				assert atom instanceof QuantEquality;
				final QuantEquality eq = (QuantEquality) atom;
				final Term lhs = eq.getLhs();
				final Term rhs = eq.getRhs();
				if (lit.isArithmetical()) { // (x = t) -> add t-1, t+1
					assert lhs instanceof TermVariable && lhs.getSort().getName() == "Int"
							&& rhs.getFreeVars().length == 0;
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
				} else {
					if (!(lhs instanceof TermVariable) && lhs.getFreeVars().length != 0) {
						assert lhs instanceof ApplicationTerm;
						addVarArgInfo((ApplicationTerm) lhs);
					}
					if (!(rhs instanceof TermVariable) && rhs.getFreeVars().length != 0) {
						assert rhs instanceof ApplicationTerm;
						addVarArgInfo((ApplicationTerm) rhs);
					}
				}
			}
		}
	}

	/**
	 * For each variable in the given term, add the uninterpreted functions and positions where it appears as argument,
	 * and the array select or store terms under which it appears to the VarInfo.
	 *
	 * @param qTerm
	 *            a function application.
	 */
	private void addVarArgInfo(final ApplicationTerm qTerm) {
		final FunctionSymbol func = qTerm.getFunction();
		final Term[] args = qTerm.getParameters();
		if (!func.isInterpreted()) {
			for (int i = 0; i < args.length; i++) {
				final Term arg = args[i];
				if (arg instanceof TermVariable) {
					final int index = getVarIndex((TermVariable) arg);
					final VarInfo varInfo = mVarInfos[index];
					varInfo.addPosition(func, i);
				} else if (arg.getFreeVars().length != 0) {
					assert arg instanceof ApplicationTerm;
					addVarArgInfo((ApplicationTerm) arg);
				}
			}
		} else if (func.getName() == "select" || func.getName() == "store") {
			for (int i = 0; i < args.length; i++) {
				final Term arg = args[i];
				if (i == 0 && arg instanceof TermVariable) {
					// TODO
				} else if (i != 0 && arg instanceof TermVariable) {
					final int index = getVarIndex((TermVariable) arg);
					final VarInfo varInfo = mVarInfos[index];
					varInfo.addArrayTerm(qTerm);
				} else if (arg.getFreeVars().length != 0) {
					assert arg instanceof ApplicationTerm;
					addVarArgInfo((ApplicationTerm) arg);
				}
			}
		} else if (func.getName() == "+" || func.getName() == "-" || func.getName() == "*") {
			final Polynomial affine = new Polynomial(qTerm);
			for (final Map<Term,Integer> smd : affine.getSummands().keySet()) {
				for (final Term factor : smd.keySet()) {
					if (factor instanceof ApplicationTerm) {
						addVarArgInfo((ApplicationTerm) factor);
					}
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
		}
		for (final ApplicationTerm arrayFuncTerm : info.mArrayTermsWithVar) {
			final FunctionSymbol func = arrayFuncTerm.getFunction();
			final String funcName = func.getName();
			final Term[] args = arrayFuncTerm.getParameters();
			final Term array = args[0];
			final CCTerm arrayCC = mQuantTheory.getCClosure().getCCTermRep(array);
			final CCTerm weakRep = arrayCC == null ? null
					: mQuantTheory.getClausifier().getArrayTheory().getWeakRep(arrayCC);
			if (args[1] == var) { // The variable is an array index
				// Get all store terms of the appropriate sort
				final Sort[] storeSorts;
				if (funcName == "store") {
					storeSorts = func.getParameterSorts();
				} else {
					storeSorts = new Sort[3];
					storeSorts[0] = func.getParameterSorts()[0];
					storeSorts[1] = func.getParameterSorts()[1];
					storeSorts[2] = func.getReturnSort();
				}
				final FunctionSymbol storeFun = mQuantTheory.getTheory().getFunction("store", storeSorts);
				final List<CCTerm> allStores = mQuantTheory.getCClosure().getAllFuncApps(storeFun);

				// Add all indices of store terms in the weak equivalence class of this array
				for (final CCTerm st : allStores) {
					final CCTerm stArr = ArrayTheory.getArrayFromStore((CCAppTerm) st);
					if (weakRep == null ? stArr.getFlatTerm().getSort() == array.getSort()
							: weakRep == mQuantTheory.getClausifier().getArrayTheory().getWeakRep(stArr)) {
						final Term indexTerm = ArrayTheory.getIndexFromStore((CCAppTerm) st).getFlatTerm();
						interestingTerms.add(indexTerm);
						if (funcName == "select" && var.getSort().getName() == "Int"
								&& !QuantUtil.isLambda(indexTerm)) {
							// For integers, add store indices +-1
							for (final Rational offset : new Rational[] { Rational.ONE, Rational.MONE }) {
								final SMTAffineTerm idxPlusMinusOneAff = new SMTAffineTerm(indexTerm);
								idxPlusMinusOneAff.add(offset);
								final Term shared = idxPlusMinusOneAff.toTerm(indexTerm.getSort());
								interestingTerms.add(shared);
							}
						}
					}
				}
				if (funcName == "select") {
					// Get all select terms of the appropriate sort
					final Sort[] selectSorts = func.getParameterSorts();
					final FunctionSymbol selectFun = mQuantTheory.getTheory().getFunction("select", selectSorts);
					final List<CCTerm> allSelects = mQuantTheory.getCClosure().getAllFuncApps(selectFun);
					// Add all select indices of select terms on arrays in the weak equivalence class of this array
					for (final CCTerm sel : allSelects) {
						final CCTerm selArr = ArrayTheory.getArrayFromSelect((CCAppTerm) sel);
						if (weakRep == null ? selArr.getFlatTerm().getSort() == array.getSort()
								: weakRep == mQuantTheory.getClausifier().getArrayTheory().getWeakRep(selArr)) {
							final CCTerm index = ArrayTheory.getIndexFromSelect((CCAppTerm) sel);
							interestingTerms.add(index.getFlatTerm());
						}
					}
				}
			}
			if (funcName == "store" && args[2] == var) { // The variable is an array value
				// Get all select terms of the appropriate sort
				final Sort[] selectSorts = Arrays.copyOf(func.getParameterSorts(), 2);
				final FunctionSymbol selectFun = mQuantTheory.getTheory().getFunction("select", selectSorts);
				final List<CCTerm> allSelects = mQuantTheory.getCClosure().getAllFuncApps(selectFun);
				// Add all select terms on arrays in the weak equivalence class of this array
				for (final CCTerm sel : allSelects) {
					final CCTerm selArr = ArrayTheory.getArrayFromSelect((CCAppTerm) sel);
					if (weakRep == null ? selArr.getFlatTerm().getSort() == array.getSort()
							: weakRep == mQuantTheory.getClausifier().getArrayTheory().getWeakRep(selArr)) {
						interestingTerms.add(sel.getFlatTerm());
					}
				}
			}
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
		private final Set<ApplicationTerm> mArrayTermsWithVar;
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
			mArrayTermsWithVar = new LinkedHashSet<>();
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

		void addArrayTerm(final ApplicationTerm term) {
			mArrayTermsWithVar.add(term);
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
