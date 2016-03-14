/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.utils;

import java.util.Collection;
import java.util.HashMap;

import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTACreator;

/**
 * Converter from arbitrary objects to NamedStates. The names of the states are integer numbers, 
 * that are counted upwards. 
 * 
 * If not reset between the two conversions, the same object will always be converted to the same state.
 *
 * @param <T> type of objects to be converted
 * 
 * @author Peter Lammich (copied from NumberedStateConctructor, written by Martin)
 */
public class NumberedStateConverter<T> implements Converter<T,NamedState<Integer>> {

	/**
	 * Stores the mapping between identification object and state.
	 */
	private HashMap<T,NamedState<Integer>> cache = new HashMap<T, NamedState<Integer>>();


	/**
	 * Stores how many distinct objects have already been identified with new states.
	 */
	private int count=0;


	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.Converter#convert(java.lang.Object)
	 */
	@Override
	public NamedState<Integer> convert(T a) {
		if (cache.containsKey(a))
			return cache.get(a);
		else {
			NamedState<Integer> newState = new NamedState<Integer>(count);
			cache.put(a,newState);
			count++;
			return newState;
		}
	}


	/**
	 * Returns all states which have been created.
	 * @return all states which have been created
	 */
	public Collection<NamedState<Integer>> getStates() {
		return cache.values();
	}


	/**
	 * Resets the internal state of this converter to the initial state, where the next index is zero and no states are known.
	 */
	public void reset() {
		cache.clear();
		count=0;
	}


	/**
	 * Converts the given automaton to an isomorphic automaton, whose states are named by integers.
	 * @param <F> Symbols
	 * @param <Q> States
	 * @param <R> Rules
	 * @param fta Automaton to be converted
	 * @return Converted automaton
	 */
	public static <F extends RankedSymbol,Q extends State, R extends FTARule<F,Q>>
	GenFTA<F,NamedState<Integer>> convert2numberedStates(FTA<F,Q, R> fta) {
		GenFTACreator<F, NamedState<Integer>> cr = new GenFTACreator<F, NamedState<Integer>>();
		return 
		FTAOps.ftaConverter(fta, NumberedStateConverter.<Q>newInstance(), 
				IdentityConverter.<F>getInstance(), 
				cr);
	}


	/**
	 * Converts the given automaton to an isomorphic automaton, whose states are named by integers.
	 * @param <F> Symbols
	 * @param <Q> States
	 * @param <R> Rules
	 * @param fta Automaton to be converted
	 * @return Converted automaton
	 */
	public static <F extends RankedSymbol,Q extends State, R extends FTARule<F,Q>>
	EasyFTA convert2numberedStatesEasy(FTA<F,Q, R> fta) {
		EasyFTACreator cr = new EasyFTACreator();
		return 
		FTAOps.ftaConverter(fta, NumberedStateConverter.<Q>newInstance(), 
				IdentityConverter.<F>getInstance(), 
				cr);
	}


	/**
	 * Static method to create a new instance. 
	 * This method saves you from typing generic type parameters.
	 * @param <T> Object type to be converted
	 * @return Fresh NumberedStateConvertor instance
	 */
	public static<T> NumberedStateConverter<T> newInstance() {
		return new NumberedStateConverter<T>();
	}

}