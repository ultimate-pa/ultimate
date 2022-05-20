/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.UnaryOperator;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class SpecificVariableAbstraction<L extends IAction>
		implements IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, VarAbsConstraints<L>, L> {

	private static final boolean ABSTRACT_TF_WITH_BRANCH_ENCODERS = false;

	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMgdScript;
	private final TransferrerWithVariableCache mTransferrer;
	private final TransFormulaAuxVarEliminator mEliminator;

	private final Set<IProgramVar> mAllProgramVars;
	private final Set<L> mAllLetters;

	private final ILattice<VarAbsConstraints<L>> mHierarchy;

	/**
	 * Create a new instance of the abstraction function.
	 *
	 * @param copyFactory
	 *            Used to create the abstracted letters
	 * @param mgdScript
	 *            Used to create the abstracted transition formulas, and for some sanity checks. The abstracted letters'
	 *            transition formulas will belong to this script.
	 * @param transferrer
	 *            If the input letters' transition formulas do not belong to {@code mgdScript}, this must be a
	 *            transferrer that transfers them from the script to which they belong to {@code mgdScript}. Otherwise,
	 *            this should be null.
	 * @param allProgramVars
	 *            The set of all variables appearing in the program to which the input letters belong.
	 * @param allLetters
	 *            The set of all letters that may be given as input.
	 */
	public SpecificVariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mgdScript,
			final TransferrerWithVariableCache transferrer, final TransFormulaAuxVarEliminator tfAuxEliminator,
			final Set<IProgramVar> allProgramVars, final Set<L> allLetters) {
		mCopyFactory = copyFactory;
		mMgdScript = mgdScript;
		mTransferrer = transferrer;
		mEliminator = tfAuxEliminator;

		mAllProgramVars = allProgramVars;
		mAllLetters = allLetters;

		mHierarchy = new VarAbsConstraints.Lattice<>(allProgramVars, mAllLetters);
	}

	@Override
	public L abstractLetter(final L inLetter, final VarAbsConstraints<L> constraints) {
		if (inLetter.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE
				|| nothingWillChange(inLetter, constraints)) {
			if (mTransferrer == null) {
				return inLetter;
			}
			return copy(inLetter, mTransferrer::transferTransFormula);
		}

		final Set<IProgramVar> transformInVars = getTransformVariablesIn(inLetter, constraints);
		final Set<IProgramVar> transformOutVars = getTransformVariablesOut(inLetter, constraints);
		return copy(inLetter, tf -> abstractTransFormula(tf, transformInVars, transformOutVars));
	}

	private L copy(final L inLetter, final UnaryOperator<UnmodifiableTransFormula> transform) {
		final UnmodifiableTransFormula newFormula = transform.apply(inLetter.getTransformula());
		final UnmodifiableTransFormula newFormulaBE;
		if (ABSTRACT_TF_WITH_BRANCH_ENCODERS && inLetter instanceof IActionWithBranchEncoders) {
			newFormulaBE =
					transform.apply(((IActionWithBranchEncoders) inLetter).getTransitionFormulaWithBranchEncoders());
		} else {
			newFormulaBE = null;
		}
		return mCopyFactory.copy(inLetter, newFormula, newFormulaBE);
	}

	private Set<IProgramVar> getTransformVariablesIn(final L letter, final VarAbsConstraints<L> constraints) {
		return DataStructureUtils.difference(letter.getTransformula().getInVars().keySet(),
				constraints.getInConstraints(letter));
	}

	private Set<IProgramVar> getTransformVariablesOut(final L letter, final VarAbsConstraints<L> constraints) {
		return DataStructureUtils.difference(letter.getTransformula().getOutVars().keySet(),
				constraints.getOutConstraints(letter));
	}

	private boolean nothingWillChange(final L inLetter, final VarAbsConstraints<L> constraints) {
		return constraints.getInConstraints(inLetter).containsAll(inLetter.getTransformula().getInVars().keySet())
				&& constraints.getOutConstraints(inLetter)
						.containsAll(inLetter.getTransformula().getOutVars().keySet());
	}

	private UnmodifiableTransFormula abstractTransFormula(UnmodifiableTransFormula utf, Set<IProgramVar> inTransform,
			Set<IProgramVar> outTransform) {
		if (mTransferrer != null) {
			// If necessary, transfer the TF to another script, and replace the transformed variables by their
			// transferred equivalents.
			utf = mTransferrer.transferTransFormula(utf);
			inTransform = mTransferrer.transferVariables(inTransform);
			outTransform = mTransferrer.transferVariables(outTransform);
		}

		final Set<TermVariable> newAuxVars = new HashSet<>();
		final Map<TermVariable, TermVariable> substitutionMap = new HashMap<>();

		for (final IProgramVar v : inTransform) {
			final TermVariable inVar = utf.getInVars().get(v);
			if (!outTransform.contains(v) && utf.getOutVars().get(v) == inVar) {
				// We cannot transform the variables independently.
				// To avoid introducing new writes, we skip abstraction of this variable.
				continue;
			}
			assert !substitutionMap.containsKey(inVar) : "Same TermVariable used for different program variables";
			final TermVariable nInVar = mMgdScript.constructFreshCopy(inVar);
			substitutionMap.put(inVar, nInVar);
			newAuxVars.add(nInVar);
		}

		for (final IProgramVar v : outTransform) {
			final TermVariable outVar = utf.getOutVars().get(v);
			if (utf.getInVars().get(v) == outVar) {
				// Either the variable was already handled above (if it is also in inTransform), or we skip it because
				// the inVar should not be abstracted and we can not separate the in- and outVar without introducing
				// new writes.
				continue;
			}
			assert !substitutionMap.containsKey(outVar) : "Same TermVariable used for different program variables";
			final TermVariable nOutVar = mMgdScript.constructFreshCopy(outVar);
			substitutionMap.put(utf.getOutVars().get(v), nOutVar);
			newAuxVars.add(nOutVar);
		}

		// Copy all auxVars, as different TFs must not share auxiliary variables.
		for (final TermVariable tv : utf.getAuxVars()) {
			final TermVariable newVariable = mMgdScript.constructFreshCopy(tv);
			substitutionMap.put(tv, newVariable);
			newAuxVars.add(newVariable);
		}

		return buildTransFormula(utf, substitutionMap, newAuxVars);
	}

	private UnmodifiableTransFormula buildTransFormula(final UnmodifiableTransFormula utf,
			final Map<TermVariable, TermVariable> substitutionMap, final Set<TermVariable> newAuxVars) {
		final Set<IProgramConst> ntc = utf.getNonTheoryConsts();
		final Set<TermVariable> be = utf.getBranchEncoders();
		final TransFormulaBuilder tfBuilder =
				new TransFormulaBuilder(utf.getInVars(), utf.getOutVars(), ntc.isEmpty(), ntc, be.isEmpty(), be, false);

		final Term substituted = Substitution.apply(mMgdScript, substitutionMap, utf.getFormula());
		final Term formula;
		if (newAuxVars.isEmpty() || mEliminator == null) {
			formula = substituted;
		} else {
			// this call modifies newAuxVars!
			formula = mEliminator.eliminate(mMgdScript, substituted, newAuxVars);
		}

		for (final TermVariable auxVar : newAuxVars) {
			tfBuilder.addAuxVar(auxVar);
		}

		tfBuilder.setFormula(formula);
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		tfBuilder.ensureInternalNormalForm();
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

		// Add all variables not used as inVars to the inConstraint.
		final Set<IProgramVar> uselessIn =
				DataStructureUtils.difference(mAllProgramVars, input.getTransformula().getInVars().keySet());
		final Set<IProgramVar> inLevel = DataStructureUtils.union(constraints.getInConstraints(input), uselessIn);

		// Add all variables not used as outVars to the outConstraint.
		final Set<IProgramVar> uselessOut =
				DataStructureUtils.difference(mAllProgramVars, input.getTransformula().getInVars().keySet());
		final Set<IProgramVar> outLevel = DataStructureUtils.union(constraints.getOutConstraints(input), uselessOut);

		// For all letters, pick the minimal abstraction level, except for the input.
		return mHierarchy.getBottom().withModifiedConstraints(input, inLevel, outLevel);
	}

	@Override
	public ILattice<VarAbsConstraints<L>> getHierarchy() {
		return mHierarchy;
	}

	public interface TransFormulaAuxVarEliminator {
		/**
		 * Eliminates auxiliary variables from formula, return new formula, and remove eliminated variables from the
		 * (modifiable) set auxVars.
		 */
		Term eliminate(final ManagedScript mgdScript, final Term formula, final Set<TermVariable> auxVars);
	}
}