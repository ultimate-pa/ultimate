package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;

/**
 * Interface for Abstract Interpretation's different automaton generators.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <VARDECL>
 */
public interface IAbstractInterpretationAutomatonGenerator<ACTION, VARDECL> {

	/**
	 * @return The nested word automaton corresponding to the result of the automaton generation.
	 */
	public NestedWordAutomaton<ACTION, VARDECL> getResult();
}
