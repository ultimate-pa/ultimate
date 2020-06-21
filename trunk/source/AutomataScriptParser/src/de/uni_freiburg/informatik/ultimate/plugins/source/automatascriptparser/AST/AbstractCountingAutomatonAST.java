package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Jacob Maxam
 */
public abstract class AbstractCountingAutomatonAST extends AutomatonAST {
	//private static final long serialVersionUID = ???;

	private final List<String> mAlphabet;
	private final List<String> mStates;
	private final List<String> mCounters;
	
	private final Map<String, String> mInitialConditions;
	private final Map<String, String> mFinalConditions;

	private final Map<String, Map<String, Set<Pair<Pair<String, Set<String>>, String>>>> mTransitions;

	public AbstractCountingAutomatonAST(final ILocation loc, final String name, final List<String> alphabet,
			final List<String> states, final List<String> counters, final Map<String, String> initConditions,
			final Map<String, String> finConditions,
			final Map<String, Map<String, Set<Pair<Pair<String, Set<String>>, String>>>> transitions) {
		super(loc, name);
		if (alphabet != null) {
			mAlphabet = alphabet;
		} else {
			mAlphabet = new ArrayList<String>();
		}
		if (states != null) {
			mStates = states;
		} else {
			mStates = new ArrayList<String>();
		}
		if (counters != null) {
			mCounters = counters;
		} else {
			mCounters = new ArrayList<String>();
		}
		if (initConditions != null) {
			mInitialConditions = initConditions;
		} else {
			mInitialConditions = new HashMap<String, String>();
		}
		if (finConditions != null) {
			mFinalConditions = finConditions;
		} else {
			mFinalConditions = new HashMap<String, String>();
		}
		if (transitions != null) {
			mTransitions = transitions;
		} else {
			mTransitions = new HashMap<String, Map<String, Set<Pair<Pair<String, Set<String>>, String>>>>();
		}
	}

	public List<String> getmAlphabet() {
		return mAlphabet;
	}

	public List<String> getmStates() {
		return mStates;
	}

	public List<String> getmCounters() {
		return mCounters;
	}

	public Map<String, String> getmInitialConditions() {
		return mInitialConditions;
	}

	public Map<String, String> getmFinalConditions() {
		return mFinalConditions;
	}

	public Map<String, Map<String, Set<Pair<Pair<String, Set<String>>, String>>>> getmTransitions() {
		return mTransitions;
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("CountingAutomaton(" + mName + "): " + "[#Alph: ");
		builder.append(mAlphabet.size());
		builder.append(" #States: ");
		builder.append(mStates.size());
		builder.append(" #Counters: ");
		builder.append(mCounters.size());
		builder.append(" #Trans: ");
		builder.append(mTransitions.size());
		builder.append("]");
		return builder.toString();
	}
}