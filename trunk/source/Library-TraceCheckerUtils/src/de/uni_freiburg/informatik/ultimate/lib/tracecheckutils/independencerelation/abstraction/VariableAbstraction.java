/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

/**
 * Implements an abstraction of actions, by (conceptually) quantifying variables that are not used in a proof candidate.
 *
 * On an implementation level, we avoid explicit quantification by the usage of auxiliary variables in
 * {@link TransFormula}s.
 *
 *
 * @author Marcel Rogg
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of actions
 */
public class VariableAbstraction<L extends IAction>
		implements IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, Set<IProgramVar>, L> {

	private final ILattice<Set<IProgramVar>> mHierarchy;
	private final SpecificVariableAbstraction<L> mSpecific;

	public VariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mgdScript,
			final Set<IProgramVar> allProgramVars) {
		mHierarchy = new UpsideDownLattice<>(new PowersetLattice<>(allProgramVars));
		mSpecific = new SpecificVariableAbstraction<>(copyFactory, mgdScript, allProgramVars, Collections.emptySet());
	}

	/**
	 * @param inLetter
	 *            is the Letter that will be abstracted
	 * @param constrainingVariables
	 *            are the Variables that describe the states of the automaton, e.g. the set of variables that
	 *            saves/preserves off of havocing a variable
	 * @return new Letter with all variables abstracted that have no occurrence in any constraining variables
	 */
	@Override
	public L abstractLetter(final L inLetter, final Set<IProgramVar> constrainingVariables) {
		// We implement this simply be delegating to SpecificVariableAbstraction with a suitable constraint.
		final VarAbsConstraints<L> constraint = mSpecific.getHierarchy().getTop().withExtendedConstraints(inLetter,
				constrainingVariables, constrainingVariables);
		return mSpecific.abstractLetter(inLetter, constraint);
	}

	// Verband - Lattice

	@Override
	public ILattice<Set<IProgramVar>> getHierarchy() {
		return mHierarchy;
	}

	@Override
	public Set<IProgramVar> restrict(final L input, final Set<IProgramVar> constrainingVars) {
		// We do not abstract infeasible letters, even if all variables are constraining.
		if (input.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return mHierarchy.getBottom();
		}

		final Set<IProgramVar> nLevel = new HashSet<>(mHierarchy.getBottom());
		nLevel.removeAll(input.getTransformula().getOutVars().keySet());
		nLevel.removeAll(input.getTransformula().getInVars().keySet());
		nLevel.addAll(constrainingVars);
		return nLevel;
	}

	@Override
	public Set<IProgramVar> refine(final Set<IProgramVar> current,
			final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
		final List<QualifiedTracePredicates> usedTracePredicates = refinement.getUsedTracePredicates();
		final Set<IProgramVar> constrainingVars = new HashSet<>();
		for (final QualifiedTracePredicates qtp : usedTracePredicates) {
			final List<IPredicate> lp = qtp.getTracePredicates().getPredicates();
			for (final IPredicate ip : lp) {
				constrainingVars.addAll(ip.getVars());
			}
		}
		constrainingVars.addAll(current);
		return constrainingVars;
	}
}