package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class RabinAutomatonAST extends AutomatonAST {
	private final List<String> mAlphabet;
	private final List<String> mStates;
	private final List<String> mInitialStates;
	private final List<String> mAcceptingStates;
	private final List<String> mFiniteStates;
	private final Map<Pair<String, String>, Set<String>> mTransitions;

	public RabinAutomatonAST(final ILocation loc, final String name, final List<String> alphabet,
			final List<String> states, final List<String> initialStates, final List<String> acceptingStates,
			final List<String> finiteStates, final TransitionListAST transitions) {
		super(loc, name);
		mAlphabet = alphabet == null ? List.of() : alphabet;
		mStates = states == null ? List.of() : states;
		mInitialStates = initialStates == null ? List.of() : initialStates;
		mAcceptingStates = acceptingStates == null ? List.of() : acceptingStates;
		mFiniteStates = finiteStates == null ? List.of() : finiteStates;
		mTransitions = transitions == null ? Map.of() : transitions.getTransitions();
	}

	public List<String> getAlphabet() {
		return mAlphabet;
	}

	public List<String> getStates() {
		return mStates;
	}

	public List<String> getInitialStates() {
		return mInitialStates;
	}

	public List<String> getAcceptingStates() {
		return mAcceptingStates;
	}

	public List<String> getFiniteStates() {
		return mFiniteStates;
	}

	public Map<Pair<String, String>, Set<String>> getTransitions() {
		return mTransitions;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("RabinAutomaton(" + mName + "): " + "[#alphabet: ");
		builder.append(mAlphabet.size());
		builder.append(" #states: ");
		builder.append(mStates.size());
		builder.append(" #initalStates: ");
		builder.append(mInitialStates.size());
		builder.append(" #acceptingStates: ");
		builder.append(mAcceptingStates.size());
		builder.append(" #finiteStates: ");
		builder.append(mFiniteStates.size());
		builder.append(" #transitions: ");
		builder.append(mTransitions.size());
		builder.append("]");
		return builder.toString();
	}
}
