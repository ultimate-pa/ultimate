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

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

public class VariableAbstraction<L extends IAction>
		implements IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, Set<IProgramVar>, L> {

	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton;
	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMscript;
	private final Set<IProgramVar> mAllProgramVars;
	private final ILattice<Set<IProgramVar>> mHierarchy;

	public VariableAbstraction(final ICopyActionFactory<L> copyFactory, final ManagedScript mscript,
			final Set<IProgramVar> allProgramVars) {
		this.automaton = null;
		mCopyFactory = copyFactory;
		mMscript = mscript;
		// TODO pass real set of all program variables
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
		final UnmodifiableTransFormula newFormula =
				abstractTransFormula(inLetter.getTransformula(), constrainingVariables);

		if (inLetter instanceof IActionWithBranchEncoders) {
			final UnmodifiableTransFormula newFormulaBE = abstractTransFormula(
					((IActionWithBranchEncoders) inLetter).getTransitionFormulaWithBranchEncoders(),
					constrainingVariables);
			return mCopyFactory.copy(inLetter, newFormula, newFormulaBE);
		}
		return mCopyFactory.copy(inLetter, newFormula, null);
	}

	/**
	 *
	 * @param utf
	 * @param constrainingVars
	 * @return
	 */

	public UnmodifiableTransFormula abstractTransFormula(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrainingVars) {
		final Set<IProgramVar> transform = new HashSet<>(utf.getInVars().keySet());
		transform.addAll(utf.getAssignedVars());
		transform.removeAll(constrainingVars);
		final Map<IProgramVar, TermVariable> nInVars = new HashMap<>(utf.getInVars());
		final Map<IProgramVar, TermVariable> nOutVars = new HashMap<>(utf.getOutVars());
		final Set<TermVariable> nAuxVars = new HashSet<>(utf.getAuxVars());
		for (final IProgramVar v : transform) {
			if (nOutVars.containsKey(v)) {
				nAuxVars.add(nOutVars.get(v));
				final TermVariable nov = mMscript.constructFreshCopy(nOutVars.get(v));
				nOutVars.put(v, nov);
			}
			if (nInVars.containsKey(v)) {
				nAuxVars.add(nInVars.get(v));
				nInVars.remove(v);
			}

		}
		final TransFormulaBuilder tfBuilder;
		final Set<IProgramConst> ntc = new HashSet<>(utf.getNonTheoryConsts());
		if (utf.getBranchEncoders().isEmpty()) {
			tfBuilder = new TransFormulaBuilder(nInVars, nOutVars, false, ntc, true, null, false);
		} else {
			final Set<TermVariable> be = new HashSet<>(utf.getBranchEncoders());
			tfBuilder = new TransFormulaBuilder(nInVars, nOutVars, false, ntc, false, be, false);
		}
		for (final TermVariable auxVar : nAuxVars) {
			tfBuilder.addAuxVar(auxVar);
		}
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		tfBuilder.setFormula(utf.getFormula());
		return tfBuilder.finishConstruction(mMscript);
	}

	// Verband - Lattice

	@Override
	public ILattice<Set<IProgramVar>> getHierarchy() {
		return mHierarchy;
	}

	@Override
	public Set<IProgramVar> restrict(final L input, final Set<IProgramVar> constrainingVars) {
		// TODO implement this properly to avoid redundant abstractions and redundant SMT calls
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
