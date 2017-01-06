package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implementation of a {@link ScopedTransitivityGenerator} with {@link Pair}s.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <C>
 *            content type; a user uses {@link Doubleton}s of {@link C} elements.
 */
public class ScopedTransitivityGeneratorPair<C> extends ScopedTransitivityGenerator<Pair<C, C>, C> {
	/**
	 * Constructor.
	 * 
	 * @param compressPaths
	 *            true iff paths should be compressed
	 */
	public ScopedTransitivityGeneratorPair(final boolean compressPaths) {
		super(compressPaths);
	}

	@Override
	protected Pair<C, C> createPair(final C content1, final C content2) {
		return new Pair<>(content1, content2);
	}

	@Override
	protected C getFirst(final Pair<C, C> pair) {
		return pair.getFirst();
	}

	@Override
	protected C getSecond(final Pair<C, C> pair) {
		return pair.getSecond();
	}

	@Override
	public boolean hasContent(final Pair<C, C> pair) {
		return mContent2node.containsKey(pair.getFirst()) && mContent2node.containsKey(pair.getSecond());
	}
}
