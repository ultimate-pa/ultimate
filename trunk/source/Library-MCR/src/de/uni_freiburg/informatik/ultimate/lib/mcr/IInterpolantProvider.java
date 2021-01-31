package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interface to construct interpolants for a given automaton.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public interface IInterpolantProvider<LETTER extends IIcfgTransition<?>> {
	/**
	 * Add interpolants for the states of {@code automaten} to {@code states2Predicates} (which is filled with some
	 * initial predicates).
	 */
	<STATE> void addInterpolants(INestedWordAutomaton<LETTER, STATE> automaton,
			Map<STATE, IPredicate> states2Predicates);
}
