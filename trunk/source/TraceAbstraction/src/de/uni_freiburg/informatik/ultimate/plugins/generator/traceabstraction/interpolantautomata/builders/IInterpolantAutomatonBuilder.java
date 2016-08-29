package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;

/**
 * An {@link IInterpolantAutomatonBuilder} is used in trace abstraction's
 * {@link AbstractCegarLoop#constructInterpolantAutomaton} to construct an interpolant automaton.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IInterpolantAutomatonBuilder<LETTER, STATE> {

	NestedWordAutomaton<LETTER, STATE> getResult();

}
