package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.List;

public class Program<S> {
	private final Class<S> mStateClazz;
	private final List<IRule<S>> mRules;

	public Program(final Class<S> stateClazz, final List<IRule<S>> rules) {
		mStateClazz = stateClazz;
		mRules = rules;
	}

	public Class<S> getStateClazz() {
		return mStateClazz;
	}

	public List<IRule<S>> getRules() {
		return mRules;
	}

}
