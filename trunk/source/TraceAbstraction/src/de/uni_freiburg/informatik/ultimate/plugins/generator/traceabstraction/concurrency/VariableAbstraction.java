package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;

public class VariableAbstraction<L extends IIcfgTransition<?>> implements IAbstraction<Set<IProgramVar>, L> {

	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton;

	public VariableAbstraction(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton) {
		this.automaton = automaton;
		final Set<IProgramVar> allVars = new HashSet<>();
		for (final IPredicate s : this.automaton.getInitialStates()) {
			final Set<IProgramVar> vars = s.getVars();
			final Iterator<IProgramVar> iti = vars.iterator();
			allVars.addAll(vars);
			final Iterable<OutgoingInternalTransition<L, IPredicate>> nextStates = automaton.internalSuccessors(s);
			// I dont untestand what this gives back
			// while (s.)

		}
	}

	@Override
	public L abstractLetter(final L inLetter, final Set<IProgramVar> setVariables) {
		final UnmodifiableTransFormula transform = inLetter.getTransformula();
		transform.getAssignedVars();
		// UnmodifiableTransFormulaBuilder
		// andere abstractionsmethode aufrufen

		return inLetter;

	}

	public UnmodifiableTransFormula abstractTransFormula(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> setProgamVars) {
		// TransFormulaBuilder aufrufem
		// SMTUtils benutzen "Quatifier exists"
		// vllt. variaben von outvars/invars nach mauxvars schieben
		// Schritt 2

		return utf;

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
