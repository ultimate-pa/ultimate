/*
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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class SpecificVariableAbstraction<L extends IAction>
		implements IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, VarAbsConstraints<L>, L> {

	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMgdScript;
	private final Set<IProgramVar> mAllProgramVars;
	private final Set<L> mAllLetters;
	private final ILattice<VarAbsConstraints<L>> mHierarchy;

	public SpecificVariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mgdScript,
			final Set<IProgramVar> allProgramVars, final Set<L> allLetters) {
		mCopyFactory = copyFactory;
		mMgdScript = mgdScript;
		mAllProgramVars = allProgramVars;
		mAllLetters = allLetters;
		mHierarchy = new VarAbsConstraints.Lattice<>(allProgramVars, mAllLetters);
	}

	@Override
	public L abstractLetter(final L inLetter, final VarAbsConstraints<L> constraints) {
		if (inLetter.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE
				|| nothingWillChange(inLetter, constraints)) {
			return inLetter;
		}
		final Set<IProgramVar> transformInVars =
				getTransformVariablesIn(inLetter.getTransformula(), constraints.getInConstraints(inLetter));
		final Set<IProgramVar> transformOutVars =
				getTransformVariablesOut(inLetter.getTransformula(), constraints.getOutConstraints(inLetter));

		final UnmodifiableTransFormula newFormula =
				abstractTransFormula(inLetter.getTransformula(), transformInVars, transformOutVars);
		assert constraints.getInConstraints(inLetter)
				.containsAll(newFormula.getInVars().keySet()) : "Abstraction must only read constrained variables";

		if (inLetter instanceof IActionWithBranchEncoders) {
			final UnmodifiableTransFormula oldFormulaBE =
					((IActionWithBranchEncoders) inLetter).getTransitionFormulaWithBranchEncoders();
			final UnmodifiableTransFormula newFormulaBE =
					abstractTransFormula(oldFormulaBE, transformInVars, transformOutVars);
			assert constraints.getInConstraints(inLetter).containsAll(
					newFormulaBE.getInVars().keySet()) : "Abstraction must only read constrained variables";

			return mCopyFactory.copy(inLetter, newFormula, newFormulaBE);
		}
		return mCopyFactory.copy(inLetter, newFormula, null);
	}

	private static Set<IProgramVar> getTransformVariablesIn(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrVars) {
		return DataStructureUtils.difference(utf.getInVars().keySet(), constrVars);
	}

	private static Set<IProgramVar> getTransformVariablesOut(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrVars) {
		return DataStructureUtils.difference(utf.getOutVars().keySet(), constrVars);
	}

	private boolean nothingWillChange(final L inLetter, final VarAbsConstraints<L> constraints) {
		return constraints.getInConstraints(inLetter).containsAll(inLetter.getTransformula().getInVars().keySet())
				&& constraints.getOutConstraints(inLetter)
						.containsAll(inLetter.getTransformula().getOutVars().keySet());
	}

	private UnmodifiableTransFormula abstractTransFormula(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> inTransform, final Set<IProgramVar> outTransform) {

		final Set<TermVariable> nAuxVars = new HashSet<>();
		final Map<TermVariable, TermVariable> substitutionMap = new HashMap<>();
		for (final IProgramVar v : inTransform) {
			final TermVariable nInVar = mMgdScript.constructFreshCopy(utf.getInVars().get(v));
			substitutionMap.put(utf.getInVars().get(v), nInVar);
			nAuxVars.add(nInVar);
		}
		for (final IProgramVar v : outTransform) {
			if (!substitutionMap.containsKey(utf.getOutVars().get(v))) {
				final TermVariable nOutVar = mMgdScript.constructFreshCopy(utf.getOutVars().get(v));
				substitutionMap.put(utf.getOutVars().get(v), nOutVar);
				nAuxVars.add(nOutVar);
			}
		}
		for (final TermVariable tv : utf.getAuxVars()) {
			final TermVariable newVariable = mMgdScript.constructFreshCopy(tv);
			substitutionMap.put(tv, newVariable);
			nAuxVars.add(newVariable);
		}

		return buildTransFormula(utf, substitutionMap, nAuxVars);
	}

	private UnmodifiableTransFormula buildTransFormula(final UnmodifiableTransFormula utf,
			final Map<TermVariable, TermVariable> substitutionMap, final Set<TermVariable> nAuxVars) {
		final Set<IProgramConst> ntc = utf.getNonTheoryConsts();
		final Set<TermVariable> be = utf.getBranchEncoders();
		final TransFormulaBuilder tfBuilder =
				new TransFormulaBuilder(utf.getInVars(), utf.getOutVars(), ntc.isEmpty(), ntc, be.isEmpty(), be, false);

		// TODO make this a method ensureInternalNormalForm() on TransFormulaBuilder
		for (final Map.Entry<IProgramVar, TermVariable> inEntry : utf.getInVars().entrySet()) {
			if (!utf.getOutVars().containsKey(inEntry.getKey()) && substitutionMap.containsKey(inEntry.getValue())) {
				// A program variable that appeared only as inVar, whose TermVariable does no longer appear in the
				// substituted formula, must be moved to outVars to preserve internal normal form.
				tfBuilder.removeInVar(inEntry.getKey());
				tfBuilder.addOutVar(inEntry.getKey(), inEntry.getValue());
			}
		}

		for (final TermVariable aV : nAuxVars) {
			tfBuilder.addAuxVar(aV);
		}
		tfBuilder.setFormula(Substitution.apply(mMgdScript, substitutionMap, utf.getFormula()));
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		final UnmodifiableTransFormula newTransFormula = tfBuilder.finishConstruction(mMgdScript);

		assert newTransFormula.getAssignedVars()
				.equals(utf.getAssignedVars()) : "Abstraction should not change assigned variables";
		assert utf.getInVars().keySet()
				.containsAll(newTransFormula.getInVars().keySet()) : "Abstraction should not read more variables";
		assert TransFormulaUtils.checkImplication(utf, newTransFormula, mMgdScript) != LBool.SAT : "not an abstraction";

		return newTransFormula;
	}

	@Override
	public VarAbsConstraints<L> refine(final VarAbsConstraints<L> constraint,
			final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
		return mHierarchy.infimum(constraint, fromAutomaton(refinement.getInfeasibilityProof()));
	}

	private VarAbsConstraints<L> fromAutomaton(final NestedWordAutomaton<L, IPredicate> automaton) {
		final Map<L, Set<IProgramVar>> inConstraints = new HashMap<>();
		final Map<L, Set<IProgramVar>> outConstraints = new HashMap<>();

		for (final IPredicate state : automaton.getStates()) {
			for (final OutgoingInternalTransition<L, IPredicate> trans : automaton.internalSuccessors(state)) {
				addConstraints(inConstraints, trans.getLetter(), state.getVars());
				addConstraints(outConstraints, trans.getLetter(), trans.getSucc().getVars());
			}
		}

		return new VarAbsConstraints<>(inConstraints, outConstraints);
	}

	private void addConstraints(final Map<L, Set<IProgramVar>> map, final L key, final Set<IProgramVar> variables) {
		final Set<IProgramVar> set = map.computeIfAbsent(key, x -> new HashSet<>());
		set.addAll(variables);
	}

	@Override
	public VarAbsConstraints<L> restrict(final L input, final VarAbsConstraints<L> constraints) {
		if (input.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return mHierarchy.getBottom();
		}

		final Set<IProgramVar> nInLevel =
				DataStructureUtils.difference(mAllProgramVars, input.getTransformula().getInVars().keySet());
		final Set<IProgramVar> nOutLevel =
				DataStructureUtils.difference(mAllProgramVars, input.getTransformula().getOutVars().keySet());
		return constraints.withExtendedConstraints(input, nInLevel, nOutLevel);
	}

	@Override
	public ILattice<VarAbsConstraints<L>> getHierarchy() {
		return mHierarchy;
	}
}