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

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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

	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMgdScript;
	private final Set<IProgramVar> mAllProgramVars;
	private final ILattice<Set<IProgramVar>> mHierarchy;

	public VariableAbstraction(final ICopyActionFactory<L> copyFactory, final CfgSmtToolkit csToolkit) {
		this(copyFactory, csToolkit.getManagedScript(), IcfgUtils.collectAllProgramVars(csToolkit));
	}

	public VariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mgdScript,
			final Set<IProgramVar> allProgramVars) {
		mCopyFactory = copyFactory;
		mMgdScript = mgdScript;
		mAllProgramVars = allProgramVars;
		mHierarchy = new UpsideDownLattice<>(new PowersetLattice<>(mAllProgramVars));
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
		if (inLetter.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE
				|| nothingWillChange(inLetter.getTransformula(), constrainingVariables)) {
			return inLetter;
		}

		final UnmodifiableTransFormula newFormula = abstractTransFormula(inLetter.getTransformula(),
				getTransformVariables(inLetter.getTransformula(), constrainingVariables));

		final L newLetter;
		if (inLetter instanceof IActionWithBranchEncoders) {
			final UnmodifiableTransFormula newFormulaBE = abstractTransFormula(
					((IActionWithBranchEncoders) inLetter).getTransitionFormulaWithBranchEncoders(),
					getTransformVariables(inLetter.getTransformula(), constrainingVariables));
			newLetter = mCopyFactory.copy(inLetter, newFormula, newFormulaBE);
		} else {
			newLetter = mCopyFactory.copy(inLetter, newFormula, null);
		}
		assert constrainingVariables.containsAll(newLetter.getTransformula().getInVars()
				.keySet()) : "Abstraction should only read constrained variables";
		return newLetter;
	}

	private static boolean nothingWillChange(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrainingVariables) {
		return constrainingVariables.containsAll(utf.getInVars().keySet())
				&& constrainingVariables.containsAll(utf.getOutVars().keySet());
	}

	private static Set<IProgramVar> getTransformVariables(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrainingVariables) {
		final Set<IProgramVar> transform = new HashSet<>(utf.getInVars().keySet());
		transform.addAll(utf.getOutVars().keySet());
		transform.removeAll(constrainingVariables);
		return transform;
	}

	/**
	 *
	 * @param utf
	 * @param constrainingVars
	 * @return
	 */
	private UnmodifiableTransFormula abstractTransFormula(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> transform) {
		// transform is the set of variables that can be havoced out
		final Set<TermVariable> nAuxVars = new HashSet<>();
		final Map<TermVariable, TermVariable> substitutionMap = new HashMap<>();
		for (final IProgramVar v : transform) {
			if (utf.getInVars().containsKey(v)) {
				final TermVariable nInVar = mMgdScript.constructFreshCopy(utf.getInVars().get(v));
				substitutionMap.put(utf.getInVars().get(v), nInVar);
				nAuxVars.add(nInVar);
			}
			if (utf.getOutVars().containsKey(v) && !substitutionMap.containsKey(utf.getOutVars().get(v))) {
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

	// Verband - Lattice

	@Override
	public ILattice<Set<IProgramVar>> getHierarchy() {
		return mHierarchy;
	}

	@Override
	public Set<IProgramVar> restrict(final L input, final Set<IProgramVar> constrainingVars) {
		// We do not abstract infeasible letters, even if all variables are constraining.
		if (input.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return mAllProgramVars;
		}

		final Set<IProgramVar> nLevel = new HashSet<>(mAllProgramVars);
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