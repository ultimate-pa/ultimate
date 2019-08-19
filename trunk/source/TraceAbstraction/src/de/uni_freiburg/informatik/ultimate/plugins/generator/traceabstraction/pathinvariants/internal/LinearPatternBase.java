/*
 * Copyright (C) 2015 David Zschocke
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A class representing an (possibly strict) linear inequality over a set of
 * {@link IProgramVar}s. A DNF over these inequalities forms a pattern as used
 * within {@link LinearInequalityInvariantPatternProcessor}.
 * @author David Zschocke, Dirk Steinmetz, Betim Musa
 */
public class LinearPatternBase extends AbstractLinearInvariantPattern {


	/**
	 * Creates a new linear inequality over a given set of {@link IProgramVar}s.
	 *
	 * @param solver
	 *            the solver to generate new function symbols in (for
	 *            coefficients and constant term)
	 * @param variables
	 *            collection of variables
	 * @param prefix
	 *            unique prefix, which is not used by any other instance of this
	 *            class or other classes accessing the same solver
	 * @param strict
	 *            true iff a strict inequality is to be generated, false iff a
	 *            non-strict inequality is to be generated
	 */
	public LinearPatternBase(final Script solver,
			final Set<IProgramVar> variables, final String prefix,
			final boolean strict) {
		super(solver, variables, prefix, strict);
	}

	protected LinearPatternBase() {

	}

	/**
	 * Returns a linear inequality corresponding to this part of the invariant,
	 * when applied to a given {@link IProgramVar}-Mapping (that is, a map assigning
	 * a {@link Term} to each {@link IProgramVar} within the inequality represented
	 * by this class).
	 *
	 * @param map
	 *            mapping to {@link Terms} to be used within the
	 *            {@link LinearInequality} generated
	 * @return linear inequality equivalent to the linear inequality represented
	 *         by this class, where each {@link IProgramVar} is replaced according
	 *         to the given mapping
	 */
	@Override
	public LinearInequality getLinearInequality(final Map<IProgramVar, Term> map) {
		assert (map.keySet().containsAll(mVariablesOfThisPattern)) : "The given map does not contain an entry for each variable of this pattern";
		final Map<IProgramVar, Term> vars2TermsForThisPattern = new HashMap<>(mVariablesOfThisPattern.size());
		for (final IProgramVar var : mVariablesOfThisPattern) {
			vars2TermsForThisPattern.put(var, map.get(var));
		}
		final LinearInequality inequality = mFunctionGenerator.generate(vars2TermsForThisPattern);
		inequality.setStrict(mStrictInequality);
		return inequality;
	}

	/**
	 * Returns the affine function \sumi a_ix_i corresponding to the
	 * linear inequality \sumi a_ix_i < b (for strict linear inequalities)
	 * or \sumi a_ix_i \le b (for non-strict linear inequalites).
	 * In addition variables given in the valuation are valuated with
	 * given values
	 * @param valuation the valuation (map for TermVariables to Rational)
	 * to use to valuate variables
	 * @return the valuated affine function corresponding to this LinearInequality
	 */
	@Override
	public AffineFunction getAffineFunction(final Map<Term, Rational> valuation){
		return mFunctionGenerator.extractAffineFunction(valuation);
	}

}
