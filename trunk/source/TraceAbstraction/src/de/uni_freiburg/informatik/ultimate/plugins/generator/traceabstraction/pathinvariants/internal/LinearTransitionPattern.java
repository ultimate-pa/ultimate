/* Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 University of Freiburg
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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.IntraproceduralReplacementVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Pattern class for transitions.
 *
 * @author Dennis Wölfing
 */
public class LinearTransitionPattern extends LinearPatternBase {
	private final Map<IProgramVar, IProgramVar> mInToOutVars;

	/**
	 * Creates a new LinearTransitionPattern.
	 *
	 * @param solver
	 *            a Script
	 * @param inVars
	 *            the input variables
	 * @param outVars
	 *            the output variables
	 * @param prefix
	 *            a prefix for the coefficients
	 * @param strict
	 *            whether a strict inequality should be generated
	 */
	public LinearTransitionPattern(final Script solver, final Set<IProgramVar> inVars, final Set<IProgramVar> outVars,
			final String prefix, final boolean strict) {
		mVariablesOfThisPattern = new HashSet<>(inVars);
		mInToOutVars = new HashMap<>();

		for (final IProgramVar var : outVars) {
			if (!mVariablesOfThisPattern.contains(var)) {
				mVariablesOfThisPattern.add(var);
				mInToOutVars.put(var, var);
			} else {
				// We need a new IProgramVar so we can put a variable as both an inVar and an outVar into the map.
				final IProgramVar outVar = new IntraproceduralReplacementVar(prefix + var.toString() + "_Out",
						var.getTerm(), var.getTermVariable());
				mVariablesOfThisPattern.add(outVar);
				mInToOutVars.put(var, outVar);
			}
		}
		mFunctionGenerator = new AffineFunctionGenerator(solver, mVariablesOfThisPattern, prefix);
		mStrictInequality = strict;
	}

	private LinearTransitionPattern(final AffineFunctionGenerator functionGenerator, final boolean strictInequality,
			final Set<IProgramVar> variables, final Map<IProgramVar, IProgramVar> inToOutVariables) {
		mFunctionGenerator = functionGenerator;
		mStrictInequality = strictInequality;
		mVariablesOfThisPattern = variables;
		mInToOutVars = inToOutVariables;
	}

	public boolean containsOutVars() {
		return !mInToOutVars.isEmpty();
	}

	public Term getCoefficientForOutVar(final IProgramVar var) {
		return mFunctionGenerator.getCoefficient(mInToOutVars.get(var));
	}

	@Override
	public LinearInequality getLinearInequality(final Map<IProgramVar, Term> inVars) {
		assert mInToOutVars.isEmpty();
		return super.getLinearInequality(inVars);
	}

	public LinearInequality getLinearInequality(final Map<IProgramVar, Term> inVars,
			final Map<IProgramVar, Term> outVars) {
		assert outVars.keySet().containsAll(mInToOutVars.keySet());
		final Map<IProgramVar, Term> map = new HashMap<>(inVars);
		for (final Map.Entry<IProgramVar, IProgramVar> entry : mInToOutVars.entrySet()) {
			map.put(entry.getValue(), outVars.get(entry.getKey()));
		}
		return super.getLinearInequality(map);
	}

	/**
	 * Creates a pattern where all coefficients are negated.
	 *
	 * @param script
	 *            a script to transform terms
	 * @return a pattern where all coefficients are negated
	 */
	public LinearTransitionPattern getPatternWithNegatedCoefficients(final Script script) {
		final AffineFunctionGenerator generator = mFunctionGenerator.getGeneratorWithNegatedCoefficients(script);
		return new LinearTransitionPattern(generator, mStrictInequality, mVariablesOfThisPattern, mInToOutVars);
	}
}
