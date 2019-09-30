package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction;

import java.util.Collection;

/**
 * An independence relation that represents the union of several independence
 * relations. This can in particular be used to combine an efficient but
 * incomplete check with a more computation-intensive check.
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class UnionIndependenceRelation<STATE, LETTER> implements IIndependenceRelation<STATE, LETTER> {

	private final Collection<IIndependenceRelation<STATE, LETTER>> mRelations;
	private final boolean mSymmetric;
	private final boolean mConditional;

	public UnionIndependenceRelation(final Collection<IIndependenceRelation<STATE, LETTER>> relations) {
		mRelations = relations;
		mSymmetric = relations.stream().allMatch(IIndependenceRelation::isSymmetric);
		mConditional = relations.stream().anyMatch(IIndependenceRelation::isConditional);
	}

	@Override
	public boolean isSymmetric() {
		return mSymmetric;
	}

	@Override
	public boolean isConditional() {
		return mConditional;
	}

	@Override
	public boolean contains(STATE state, LETTER a, LETTER b) {
		return mRelations.stream().anyMatch(r -> r.contains(state, a, b));
	}
}
