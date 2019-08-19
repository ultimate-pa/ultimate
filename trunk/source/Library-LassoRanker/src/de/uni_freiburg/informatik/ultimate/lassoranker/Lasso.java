/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * This is a lasso program represented by a stem and a loop transition. The state before the stem is called the initial
 * state (init), and the state after the stem, before and after the loop is called honda.
 *
 * This is best explained using ascii art:
 *
 * <pre>
 *                         ______
 *            stem        /      \
 * (init) ---------->  (honda)    | loop
 *                       ^        |
 *                        \______/
 * </pre>
 *
 * @author Jan Leike
 */
public class Lasso implements Serializable {
	private static final long serialVersionUID = 8922273828007750770L;

	/**
	 * The stem transition
	 */
	private final LinearTransition mStem;

	/**
	 * The loop transition
	 */
	private final LinearTransition mLoop;

	/**
	 * Construct a new lasso program
	 *
	 * @param stem
	 *            the stem transition, can be null
	 * @param loop
	 *            the loop transition, can be null
	 */
	public Lasso(final LinearTransition stem, final LinearTransition loop) {
		final LinearTransition newStem = balanceVariablesStem(stem, loop);
		final LinearTransition newLoop = balanceVariablesLoop(stem, loop);
		mStem = newStem == null ? LinearTransition.getTranstionTrue() : newStem;
		mLoop = newLoop == null ? LinearTransition.getTranstionTrue() : newLoop;

	}

	/**
	 * @return the stem (is never null)
	 */
	public LinearTransition getStem() {
		assert mStem != null;
		return mStem;
	}

	/**
	 * @return the loop (is never null)
	 */
	public LinearTransition getLoop() {
		assert mLoop != null;
		return mLoop;
	}

	/**
	 * @return the number of variables occurring in the preprocessed loop transition
	 */
	public int getLoopVarNum() {
		return mLoop.getVariables().size();
	}

	/**
	 * @return the number of variables occurring in the preprocessed stem transition
	 */
	public int getStemVarNum() {
		return mStem.getVariables().size();
	}

	/**
	 * @return the number of disjuncts in the loop transition's DNF after preprocessing
	 */
	public int getLoopDisjuncts() {
		return mLoop.getNumPolyhedra();
	}

	/**
	 * @return the number of disjuncts in the stem transition's DNF after preprocessing
	 */
	public int getStemDisjuncts() {
		return mStem.getNumPolyhedra();
	}

	/**
	 * @return all RankVars that occur in the lasso
	 */
	public Collection<IProgramVar> getAllRankVars() {
		final Collection<IProgramVar> rankVars = new LinkedHashSet<>();
		rankVars.addAll(mStem.getInVars().keySet());
		rankVars.addAll(mStem.getOutVars().keySet());
		rankVars.addAll(mLoop.getInVars().keySet());
		rankVars.addAll(mLoop.getOutVars().keySet());
		return rankVars;
	}

	/**
	 * Provide guesses for eigenvalues of the loop.
	 *
	 * This procedure is neither sound nor complete: there might be eigenvalues that are not found by this procedure and
	 * this procedure might return values that are not eigenvalues of the loop.
	 *
	 * The result of this is used as guesses for Motzkin coefficients in the termination analysis and for lambda in the
	 * nontermination analysis. This allows us to handle some more complicated examples while relying only on linear
	 * constraint solving.
	 *
	 * This method works as follows. If there is a statement
	 *
	 * <pre>
	 * x = 2 * y + 5
	 * </pre>
	 *
	 * we guess the eigenvalue 2 if we can prove that the loop disjunct implies x = y.
	 *
	 * The returned values always contain 0 and 1.
	 *
	 * @param includeNegative
	 *            whether to include negative guesses
	 * @return an array of guesses for the loop's eigenvalues
	 */
	public Rational[] guessEigenvalues(final boolean includeNegative) {
		final Set<Rational> motzkinCoeffs = new HashSet<>();
		motzkinCoeffs.add(Rational.ZERO);
		motzkinCoeffs.add(Rational.ONE);
		for (final List<LinearInequality> polyhedron : mLoop.getPolyhedra()) {
			// Find aliases for variables
			final Map<Term, Set<Term>> aliases = new HashMap<>();
			for (final LinearInequality li : polyhedron) {
				// If li is 0 <= a*x + b*y with a == -b and a != 0 != b
				// then put x -> y into aliases
				if (!li.isStrict() && li.getConstant().isZero() && li.getVariables().size() == 2) {
					final Term[] vars = li.getVariables().toArray(new Term[2]);
					final AffineTerm at0 = li.getCoefficient(vars[0]);
					final AffineTerm at1 = li.getCoefficient(vars[1]);
					assert !at0.isZero();
					assert !at1.isZero();
					if (at0.isConstant() && at1.isConstant() && at0.getConstant().equals(at1.getConstant().negate())) {
						Term var0 = vars[0];
						Term var1 = vars[1];
						if (at0.getConstant().isNegative()) {
							// Swap var0 and var1
							final Term var2 = var0;
							var0 = var1;
							var1 = var2;
						}
						if (!aliases.containsKey(var0)) {
							aliases.put(var0, new HashSet<Term>());
						}
						aliases.get(var0).add(var1);
					}
				}
			}

			for (final Map.Entry<IProgramVar, TermVariable> entry : mLoop.getOutVars().entrySet()) {
				final IProgramVar rkVar = entry.getKey();
				final Term outVar = entry.getValue();

				// Find possible aliases
				if (!mLoop.getInVars().containsKey(rkVar)) {
					continue;
				}
				final List<Term> possibleInVars = new ArrayList<>();
				final Term inVar = mLoop.getInVars().get(rkVar);
				possibleInVars.add(inVar);
				if (aliases.containsKey(inVar)) {
					for (final Term aliasVar : aliases.get(inVar)) {
						if (aliases.containsKey(aliasVar) && aliases.get(aliasVar).contains(inVar)) {
							possibleInVars.add(aliasVar);
						}
					}
				}

				for (final LinearInequality li : polyhedron) {
					for (final Term aliasVar : possibleInVars) {
						final AffineTerm cIn = li.getCoefficient(aliasVar);
						final AffineTerm cOut = li.getCoefficient(outVar);
						if (!cIn.isZero() && !cOut.isZero()) {
							// inVar and outVar occur in this linear inequality
							assert cIn.isConstant();
							assert cOut.isConstant();
							final Rational eigenv = cIn.getConstant().div(cOut.getConstant()).negate();
							if (!eigenv.isNegative() || includeNegative) {
								motzkinCoeffs.add(eigenv);
							}
						}
					}
				}
			}
		}
		return motzkinCoeffs.toArray(new Rational[motzkinCoeffs.size()]);
	}

	/**
	 * Add all inVars of the loop as in- and outVars of the stem.
	 *
	 * This ensures that (global) valuations for variables (e.g. those generated in the nontermination analysis) stay
	 * constant in transitions where these variables are not explicitly scoped.
	 */
	private static LinearTransition balanceVariablesStem(final LinearTransition stem, final LinearTransition loop) {
		if (stem == null || loop == null) {
			// nothing to do
			return stem;
		}
		// Add variables existing in the loop to the stem
		final Map<IProgramVar, TermVariable> addVars = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : loop.getInVars().entrySet()) {
			if (!stem.getInVars().containsKey(entry.getKey()) && !stem.getOutVars().containsKey(entry.getKey())) {
				addVars.put(entry.getKey(), entry.getValue());
			}
		}
		if (!addVars.isEmpty()) {
			// Because the variable maps in LinearTransition are immutable,
			// make a new transition and replace the old one
			final Map<IProgramVar, TermVariable> inVars = new HashMap<>(stem.getInVars());
			final Map<IProgramVar, TermVariable> outVars = new HashMap<>(stem.getOutVars());
			inVars.putAll(addVars);
			outVars.putAll(addVars);
			return new LinearTransition(stem.getPolyhedra(), inVars, outVars);
		}
		return stem;
	}

	/**
	 * Add all outVars of the stem as in- and outVars of the loop.
	 *
	 * This ensures that (global) valuations for variables (e.g. those generated in the nontermination analysis) stay
	 * constant in transitions where these variables are not explicitly scoped.
	 */
	private static LinearTransition balanceVariablesLoop(final LinearTransition stem, final LinearTransition loop) {
		if (stem == null || loop == null) {
			// nothing to do
			return loop;
		}

		// Add variables existing in the stem to the loop
		final Map<IProgramVar, TermVariable> addVars = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : stem.getOutVars().entrySet()) {
			if (!loop.getInVars().containsKey(entry.getKey()) && !loop.getOutVars().containsKey(entry.getKey())) {
				addVars.put(entry.getKey(), entry.getValue());
			}
		}
		if (!addVars.isEmpty()) {
			// Because the variable maps in LinearTransition are immutable,
			// make a new transition and replace the old one
			final Map<IProgramVar, TermVariable> inVars = new HashMap<>(loop.getInVars());
			final Map<IProgramVar, TermVariable> outVars = new HashMap<>(loop.getOutVars());
			inVars.putAll(addVars);
			outVars.putAll(addVars);
			return new LinearTransition(loop.getPolyhedra(), inVars, outVars);
		}
		return loop;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Stem: ");
		sb.append(mStem);
		sb.append("\nLoop: ");
		sb.append(mLoop);
		return sb.toString();
	}
}
