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
import java.util.stream.Collectors;

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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitSubSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class SpecificVariableAbstraction<L extends IAction>
		implements IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, VarAbsConstraints<L>, L> {

	private static final boolean ABSTRACT_TF_WITH_BRANCH_ENCODERS = false;

	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMgdScript;
	private final TransferrerWithVariableCache mTransferrer;
	private final TransFormulaAuxVarEliminator mEliminator;

	private final BitSubSet.Factory<IProgramVar> mFactory;

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
	 * @param tfAuxEliminator
	 *            Used to eliminate auxiliary variables from the abstracted transition formula. May be null.
	 * @param allLetters
	 *            The set of all letters that may be given as input.
	 * @param allProgramVars
	 *            The set of all variables appearing in the program to which the input letters belong.
	 */
	public SpecificVariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mgdScript,
			final TransferrerWithVariableCache transferrer, final TransFormulaAuxVarEliminator tfAuxEliminator,
			final Set<L> allLetters, final Set<IProgramVar> allProgramVars) {
		this(copyFactory, mgdScript, transferrer, tfAuxEliminator, allLetters, new BitSubSet.Factory<>(allProgramVars));
	}

	SpecificVariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mgdScript,
			final TransferrerWithVariableCache transferrer, final TransFormulaAuxVarEliminator tfAuxEliminator,
			final Set<L> allLetters, final BitSubSet.Factory<IProgramVar> factory) {
		mCopyFactory = copyFactory;
		mMgdScript = mgdScript;
		mTransferrer = transferrer;
		mEliminator = tfAuxEliminator;

		mFactory = factory;
		mHierarchy = new VarAbsConstraints.Lattice<>(allLetters, mFactory);
	}

	@Override
	public L abstractLetter(final L inLetter, final VarAbsConstraints<L> constraints) {
		final var inVars = inVars(inLetter);
		final var outVars = outVars(inLetter);

		if (inLetter.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE
				|| nothingWillChange(inLetter, inVars, outVars, constraints)) {
			if (mTransferrer == null) {
				return inLetter;
			}
			return copy(inLetter, mTransferrer::transferTransFormula);
		}

		final BitSubSet<IProgramVar> transformInVars = getTransformVariablesIn(inLetter, inVars, constraints);
		final BitSubSet<IProgramVar> transformOutVars = getTransformVariablesOut(inLetter, outVars, constraints);
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

	private BitSubSet<IProgramVar> getTransformVariablesIn(final L letter, final BitSubSet<IProgramVar> inVars,
			final VarAbsConstraints<L> constraints) {
		return mFactory.difference(inVars, constraints.getInConstraints(letter));
	}

	private BitSubSet<IProgramVar> getTransformVariablesOut(final L letter, final BitSubSet<IProgramVar> outVars,
			final VarAbsConstraints<L> constraints) {
		return mFactory.difference(outVars, constraints.getOutConstraints(letter));
	}

	private boolean nothingWillChange(final L inLetter, final BitSubSet<IProgramVar> inVars,
			final BitSubSet<IProgramVar> outVars, final VarAbsConstraints<L> constraints) {
		return constraints.getInConstraints(inLetter).containsAll(inVars)
				&& constraints.getOutConstraints(inLetter).containsAll(outVars);
	}

	private UnmodifiableTransFormula abstractTransFormula(UnmodifiableTransFormula utf,
			final BitSubSet<IProgramVar> inTransform, final BitSubSet<IProgramVar> outTransform) {
		// If necessary, transfer the TF to another script.
		if (mTransferrer != null) {
			utf = mTransferrer.transferTransFormula(utf);
		}

		final Set<TermVariable> newAuxVars = new HashSet<>();
		final Map<TermVariable, TermVariable> substitutionMap = new HashMap<>();

		for (IProgramVar v : inTransform) {
			if (mTransferrer != null) {
				v = mTransferrer.transferProgramVar(v);
			}

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

		for (IProgramVar v : outTransform) {
			if (mTransferrer != null) {
				v = mTransferrer.transferProgramVar(v);
			}

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

		// Compute the new formula
		final Term substituted = Substitution.apply(mMgdScript, substitutionMap, utf.getFormula());
		final Term formula;
		if (newAuxVars.isEmpty() || mEliminator == null) {
			formula = substituted;
		} else {
			// this call modifies newAuxVars!
			formula = mEliminator.eliminate(mMgdScript, substituted, newAuxVars);
		}

		// Collect the non-theory constants that (actually) appear in the (possibly simplified) formula.
		Set<IProgramConst> ntc = utf.getNonTheoryConsts();
		if (!ntc.isEmpty()) {
			final Set<ApplicationTerm> constantsInFormula = SmtUtils.extractConstants(formula, true);
			ntc = ntc.stream().filter(c -> constantsInFormula.contains(c.getDefaultConstant()))
					.collect(Collectors.toSet());
		}

		// Assemble the UnmodifiableTransFormula
		final Set<TermVariable> be = utf.getBranchEncoders();
		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(utf.getInVars(), utf.getOutVars(), ntc.isEmpty(),
				ntc, be.isEmpty(), be, newAuxVars.isEmpty());
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
		final Map<L, BitSubSet<IProgramVar>> inConstraints = new HashMap<>();
		final Map<L, BitSubSet<IProgramVar>> outConstraints = new HashMap<>();

		for (final IPredicate state : automaton.getStates()) {
			for (final OutgoingInternalTransition<L, IPredicate> trans : automaton.internalSuccessors(state)) {
				addConstraints(inConstraints, trans.getLetter(), state.getVars());
				addConstraints(outConstraints, trans.getLetter(), trans.getSucc().getVars());
			}
		}

		return new VarAbsConstraints<>(inConstraints, outConstraints, mFactory.empty());
	}

	private void addConstraints(final Map<L, BitSubSet<IProgramVar>> map, final L key,
			final Set<IProgramVar> variables) {
		final BitSubSet<IProgramVar> oldValue = map.get(key);
		final BitSubSet<IProgramVar> newValue;
		if (oldValue == null) {
			newValue = mFactory.valueOf(variables);
		} else {
			newValue = mFactory.union(oldValue, mFactory.valueOf(variables));
		}
		map.put(key, newValue);
	}

	private BitSubSet<IProgramVar> inVars(final L letter) {
		return mFactory.valueOf(letter.getTransformula().getInVars().keySet());
	}

	private BitSubSet<IProgramVar> outVars(final L letter) {
		return mFactory.valueOf(letter.getTransformula().getOutVars().keySet());
	}

	@Override
	public VarAbsConstraints<L> restrict(final L input, final VarAbsConstraints<L> constraints) {
		if (input.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return mHierarchy.getBottom();
		}

		// Add all variables not used as inVars to the inConstraint.
		final BitSubSet<IProgramVar> uselessIn = mFactory.complement(inVars(input));
		final BitSubSet<IProgramVar> inLevel = mFactory.union(constraints.getInConstraints(input), uselessIn);

		// Add all variables not used as outVars to the outConstraint.
		final BitSubSet<IProgramVar> uselessOut = mFactory.complement(outVars(input));
		final BitSubSet<IProgramVar> outLevel = mFactory.union(constraints.getOutConstraints(input), uselessOut);

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
