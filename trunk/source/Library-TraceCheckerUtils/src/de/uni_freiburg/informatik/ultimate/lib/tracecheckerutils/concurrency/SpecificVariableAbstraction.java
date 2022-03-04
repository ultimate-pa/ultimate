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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class SpecificVariableAbstraction<L extends IAction>
		implements IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, VarAbsConstraints<L>, L> {

	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton;
	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMscript;
	private final Set<IProgramVar> mAllProgramVars;
	private final Set<L> mAllLetters;
	private final ILattice<VarAbsConstraints<L>> mHierarchy;

	public SpecificVariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mscript,
			final Set<IProgramVar> allProgramVars, final Set<L> allLetters) {
		this.automaton = null;
		mCopyFactory = copyFactory;
		mMscript = mscript;
		mAllProgramVars = allProgramVars;
		mAllLetters = allLetters;
		mHierarchy = new VarAbLattice<>(allProgramVars, mAllLetters);
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
				getTransformVariablesIn(inLetter.getTransformula(), constraints.getOutConstraints(inLetter));
		final UnmodifiableTransFormula newFormula =
				abstractTransFormula(inLetter.getTransformula(), transformInVars, transformOutVars);
		if (inLetter instanceof IActionWithBranchEncoders) {
			final UnmodifiableTransFormula newFormulaBE = abstractTransFormula(
					((IActionWithBranchEncoders) inLetter).getTransitionFormulaWithBranchEncoders(), transformInVars,
					transformOutVars);
			return mCopyFactory.copy(inLetter, newFormula, newFormulaBE);
		}
		return mCopyFactory.copy(inLetter, newFormula, null);
	}

	public static Set<IProgramVar> getTransformVariablesIn(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrVars) {
		final Set<IProgramVar> transform = new HashSet<>(utf.getInVars().keySet());
		transform.removeAll(constrVars);
		return transform;
	}

	public static Set<IProgramVar> getTransformVariablesOut(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrVars) {
		final Set<IProgramVar> transform = new HashSet<>(utf.getOutVars().keySet());
		transform.removeAll(constrVars);
		return transform;
	}

	private boolean nothingWillChange(final L inLetter, final VarAbsConstraints<L> constraints) {
		// Is this sound? If every Variable, that can be assigned is in InVars .. and so on?
		if (constraints.getInConstraints(inLetter).containsAll(inLetter.getTransformula().getInVars().keySet())
				&& constraints.getOutConstraints(inLetter)
						.containsAll(inLetter.getTransformula().getInVars().keySet())) {
			return true;
		}
		return false;
	}

	public UnmodifiableTransFormula abstractTransFormula(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> inTransform, final Set<IProgramVar> outTransform) {

		final Set<TermVariable> nAuxVars = new HashSet<>(utf.getAuxVars());
		final Map<TermVariable, TermVariable> substitutionMap = new HashMap<>();
		for (final IProgramVar v : inTransform) {
			final TermVariable nInVar = mMscript.constructFreshCopy(utf.getInVars().get(v));
			substitutionMap.put(utf.getInVars().get(v), nInVar);
			nAuxVars.add(nInVar);
			if (outTransform.contains(v) && utf.getInVars().get(v) == utf.getOutVars().get(v)) {
				outTransform.remove(v);
			}
		}
		for (final IProgramVar v : outTransform) {
			final TermVariable nOutVar = mMscript.constructFreshCopy(utf.getOutVars().get(v));
			substitutionMap.put(utf.getOutVars().get(v), nOutVar);
			nAuxVars.add(nOutVar);
		}

		return buildTransFormula(utf, substitutionMap, nAuxVars);
	}

	UnmodifiableTransFormula buildTransFormula(final UnmodifiableTransFormula utf,
			final Map<TermVariable, TermVariable> substitutionMap, final Set<TermVariable> nAuxVars) {
		final TransFormulaBuilder tfBuilder;
		final Set<IProgramConst> ntc = new HashSet<>(utf.getNonTheoryConsts());
		if (utf.getBranchEncoders().isEmpty()) {
			tfBuilder = new TransFormulaBuilder(utf.getInVars(), utf.getOutVars(), false, ntc, true, null, false);
		} else {
			final Set<TermVariable> be = new HashSet<>(utf.getBranchEncoders());
			tfBuilder = new TransFormulaBuilder(utf.getInVars(), utf.getOutVars(), false, ntc, false, be, false);
		}
		for (final TermVariable aV : nAuxVars) {
			tfBuilder.addAuxVar(aV);
		}
		tfBuilder.setFormula(Substitution.apply(mMscript, substitutionMap, utf.getFormula()));
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		final UnmodifiableTransFormula newTransFormula = tfBuilder.finishConstruction(mMscript);

		assert newTransFormula.getAssignedVars()
				.equals(utf.getAssignedVars()) : "Abstraction should not change assigned variables";
		assert utf.getInVars().keySet()
				.containsAll(newTransFormula.getInVars().keySet()) : "Abstraction should not read more variables";
		// assert constrainingVars.containsAll(abstracted.getInVars().keySet()) : "Abstraction should only read
		// constrained variables";

		assert TransFormulaUtils.checkImplication(utf, newTransFormula, mMscript) != LBool.SAT : "not an abstraction";
		return newTransFormula;
	}

	@Override
	public VarAbsConstraints<L> refine(final VarAbsConstraints<L> constraint,
			final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
		final Map<L, Set<IProgramVar>> nInConstr = new HashMap<>(constraint.getInContraintsMap());
		final Map<L, Set<IProgramVar>> nOutConstr = new HashMap<>(constraint.getOutContraintsMap());

		final Set<IPredicate> states = refinement.getInfeasibilityProof().getStates();
		for (final IPredicate p : states) {
			for (final IncomingInternalTransition<L, IPredicate> it : refinement.getInfeasibilityProof()
					.internalPredecessors(p)) {
				if (nInConstr.containsKey(it.getLetter())) {
					nInConstr.get(it.getLetter()).addAll(it.getPred().getVars());
				} else {
					nInConstr.put(it.getLetter(), it.getPred().getVars());
				}

			}
			for (final OutgoingInternalTransition<L, IPredicate> it : refinement.getInfeasibilityProof()
					.internalSuccessors(p)) {
				if (nOutConstr.containsKey(it.getLetter())) {
					nOutConstr.get(it.getLetter()).addAll(it.getSucc().getVars());
				} else {
					nOutConstr.put(it.getLetter(), it.getSucc().getVars());
				}
			}
		}

		return new VarAbsConstraints<>(nInConstr, nOutConstr);
	}

	@Override
	public VarAbsConstraints<L> restrict(final L input, final VarAbsConstraints<L> constraints) {
		// TODO implement this properly to avoid redundant abstractions and redundant SMT calls

		final Set<IProgramVar> nInLevel = new HashSet<>(mAllProgramVars);
		final Set<IProgramVar> nOutLevel = new HashSet<>(mAllProgramVars);
		nOutLevel.removeAll(input.getTransformula().getOutVars().keySet());
		nInLevel.removeAll(input.getTransformula().getInVars().keySet());
		final Map<L, Set<IProgramVar>> nInConstr = new HashMap<>(constraints.getInContraintsMap());
		final Map<L, Set<IProgramVar>> nOutConstr = new HashMap<>(constraints.getOutContraintsMap());
		if (nInConstr.containsKey(input)) {
			nInConstr.get(input).addAll(nInLevel);
		} else {
			nInConstr.put(input, nInLevel);
		}
		if (nOutConstr.containsKey(input)) {
			nOutConstr.get(input).addAll(nOutLevel);
		} else {
			nInConstr.put(input, nOutLevel);
		}
		return new VarAbsConstraints<>(nInConstr, nOutConstr);
	}

	@Override
	public ILattice<VarAbsConstraints<L>> getHierarchy() {
		return mHierarchy;
	}
}