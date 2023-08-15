package de.uni_freiburg.informatik.ultimate.automata.dynamic_stratified_reduction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;

public interface IIndependenceInducedByAbstraction<S,L> {
	/**
	 * 
	 * @param freeVariables
	 * 			Set of program variables that are not abstracted away
	 * @return
	 * 			The independence relation induced by abstracting all program variables but the free variables
	 */
	public IIndependenceRelation<S, L> getInducedIndependence(Set<L> freeVariables);

}
