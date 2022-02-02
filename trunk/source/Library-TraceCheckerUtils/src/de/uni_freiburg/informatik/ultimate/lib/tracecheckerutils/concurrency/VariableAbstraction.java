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

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;

public class VariableAbstraction<L extends IIcfgTransition<?>> implements IAbstraction<Set<IProgramVar>, L> {

	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton;
	private final ICopyActionFactory<L> mCopyFactory;

	public VariableAbstraction(final ICopyActionFactory<L> copyFactory) {
		this.automaton = null;
		mCopyFactory = copyFactory;
		// We need a Script to build a new TransFormula
		/*
		 * this.automaton = automaton; final Set<IProgramVar> allVars = new HashSet<>(); for (final IPredicate s :
		 * this.automaton.getInitialStates()) { final Set<IProgramVar> vars = s.getVars(); final Iterator<IProgramVar>
		 * iti = vars.iterator(); allVars.addAll(vars); final Iterable<OutgoingInternalTransition<L, IPredicate>>
		 * nextStates = automaton.internalSuccessors(s); // I dont untestand what this gives back // while (s.)
		 *
		 * }
		 */
	}

	/**
	 * @param inLetter
	 *            is the Letter that will be abstracted
	 * @param setVariables
	 *            are the Variables that describe the states of the automaton, e.g. the set of variables that
	 *            saves/preserves off of havocing a variable
	 * @return new Letter with all variables abstracted that have no occurrence in any constraining variables
	 */
	@Override
	public L abstractLetter(final L inLetter, final Set<IProgramVar> setVariables) {
		final UnmodifiableTransFormula newFormula = abstractTransFormula(inLetter.getTransformula(), setVariables);
		return mCopyFactory.copy(inLetter, newFormula, newFormula);
	}

	/**
	 *
	 * @param utf
	 * @param setVariables
	 * @return
	 */

	public UnmodifiableTransFormula abstractTransFormula(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> setVariables) {
		final Set<IProgramVar> transform = utf.getInVars().keySet();
		transform.addAll(utf.getAssignedVars());
		transform.removeAll(setVariables);

		final Map<IProgramVar, TermVariable> nInVars = utf.getInVars();
		final Map<IProgramVar, TermVariable> nOutVars = utf.getOutVars();
		final Set<TermVariable> nAuxVars = utf.getAuxVars();
		for (final IProgramVar v : transform) {
			// Case: The variable to havoce out is not the variable that is freshly assigned, but one that is a part of
			// the assignment
			if (nInVars.containsKey(v)) {
				nInVars.remove(v);
				nAuxVars.add(v.getTermVariable());
			}
			// Case: the variabel is the varable that is freshly assigned
			if (nOutVars.containsKey(v)) {
				nAuxVars.add(v.getTermVariable());
				// what is with the mFormula? Shoudnt we change something there?
			}
		}
		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(nInVars, nOutVars, false,
				utf.getNonTheoryConsts(), false, utf.getBranchEncoders(), false);
		// tfBuilder.addProgramConst(utf.getNonTheoryConsts()); //
		tfBuilder.setInfeasibility(utf.isInfeasible());
		tfBuilder.setFormula(utf.getFormula());
		final UnmodifiableTransFormula newFormula = tfBuilder.finishConstruction(null); // Script :'(

		return newFormula;

	}

	public L abstractLetterSOMETHINGELSE(final L inLetter) {
		// Abstract Letters here
		final UnmodifiableTransFormula transform = inLetter.getTransformula();
		final Set<IProgramVar> asVars = transform.getAssignedVars();
		for (final IProgramVar av : asVars) {
			// If av is not contained by the variables, that are used in the states, they can be abstracted

		}
		final UnmodifiableTransFormula transformedLetter;
		return inLetter;
	}

	public L abstractLetterOccurence(final L Letter, final IPredicate inState, final IPredicate outState) {

		return Letter;
	}

	// Verband - Lattice

	@Override
	public ILattice<Set<IProgramVar>> getHierarchy() {
		// TODO Auto-generated method stub
		return new PowersetLattice();
	}

}
