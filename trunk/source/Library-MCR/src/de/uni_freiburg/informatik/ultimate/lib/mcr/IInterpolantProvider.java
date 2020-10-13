package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interface to construct interpolants for a given trace with precondition and postcondition.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public interface IInterpolantProvider<LETTER> {
	<STATE> Map<STATE, IPredicate> getInterpolants(INestedWordAutomaton<LETTER, STATE> automaton,
			Map<STATE, IPredicate> stateMap);
}
