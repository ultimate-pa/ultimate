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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.xnf.Dnf;

/**
 * The default strategy for danger invariants.
 *
 * @author Dennis Wölfing
 */
public class DangerInvariantPatternStrategy extends LocationIndependentLinearInequalityInvariantPatternStrategy {
	private final Map<IcfgEdge, Set<Term>> mIntegerCoefficients;

	public DangerInvariantPatternStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat,
			final int maxRounds, final Set<IProgramVar> allProgramVariables, final Set<IProgramVar> patternVariables,
			final boolean alwaysStrictAndNonStrictCopies, final boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables, patternVariables, alwaysStrictAndNonStrictCopies,
				useStrictInequalitiesAlternatingly);
		mIntegerCoefficients = new HashMap<>();
	}

	@Override
	public Set<IProgramVar> getPatternVariablesForLocation(final IcfgLocation location, final int round) {
		return Collections.unmodifiableSet(mAllProgramVariables);
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getPatternForTransition(final IcfgEdge transition, final int round,
			final Script solver, final String prefix) {
		mIntegerCoefficients.put(transition, new HashSet<>());

		final TransFormula tf = transition.getTransformula();
		final Map<IProgramVar, TermVariable> inVars = tf.getInVars();
		final Map<IProgramVar, TermVariable> outVars = tf.getOutVars();
		final List<TermVariable> usedVars = Arrays.asList(tf.getFormula().getFreeVars());

		final Set<IProgramVar> havocedVars = new HashSet<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : outVars.entrySet()) {
			if (!usedVars.contains(entry.getValue())) {
				havocedVars.add(entry.getKey());
			}
		}

		final Collection<AbstractLinearInvariantPattern> conjuncts = new ArrayList<>();
		if (transition.getSource() != null && transition.getSource().getOutgoingEdges().size() > 1) {
			conjuncts.add(new LinearTransitionPattern(solver, inVars.keySet(), Collections.emptySet(),
					prefix + "_" + newPrefix(), false));
		}

		for (final IProgramVar havocedVar : havocedVars) {
			final LinearTransitionPattern pattern1 = new LinearTransitionPattern(solver, inVars.keySet(),
					Collections.singleton(havocedVar), prefix + "_" + newPrefix(), false);
			final LinearTransitionPattern pattern2 = pattern1.getPatternWithNegatedCoefficients(solver);
			conjuncts.add(pattern1);
			conjuncts.add(pattern2);
			final Term primedCoefficient = pattern1.getCoefficientForOutVar(havocedVar);
			solver.assertTerm(
					solver.term("=", primedCoefficient, Rational.ONE.toTerm(solver.sort(SmtSortUtils.REAL_SORT))));
			for (final Term coefficient : pattern1.getCoefficients()) {
				mIntegerCoefficients.get(transition).add(coefficient);
			}
		}

		return new Dnf<>(conjuncts);
	}

	@Override
	public Set<Term> getIntegerCoefficientsForTransition(final IcfgEdge transition) {
		return Collections.unmodifiableSet(mIntegerCoefficients.get(transition));
	}
}
