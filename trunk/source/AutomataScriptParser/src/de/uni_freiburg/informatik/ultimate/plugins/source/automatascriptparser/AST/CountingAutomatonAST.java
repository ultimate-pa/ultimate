package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Jacob Maxam
 */
public class CountingAutomatonAST extends AbstractCountingAutomatonAST {
	//private static final long serialVersionUID = ???;
	
	public CountingAutomatonAST(ILocation loc, String name, List<String> alphabet, List<String> states,
			List<String> counters, Map<String, String> initConditions, Map<String, String> finConditions,
			Map<String, Map<String, Set<Pair<Pair<String, Set<String>>, String>>>> transitions) {
		super(loc, name, alphabet, states, counters, initConditions, finConditions, transitions);
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("CountingAutomaton(" + mName + "): " + "[#Alph: ");
		builder.append(getmAlphabet().size());
		builder.append(" #States: ");
		builder.append(getmStates().size());
		builder.append(" #Counters: ");
		builder.append(getmCounters().size());
		builder.append(" #Trans: ");
		builder.append(getmTransitions().size());
		builder.append("]");
		return builder.toString();
	}

}
