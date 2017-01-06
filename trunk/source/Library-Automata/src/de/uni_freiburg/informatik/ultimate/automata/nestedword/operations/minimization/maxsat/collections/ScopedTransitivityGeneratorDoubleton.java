package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Implementation of a {@link ScopedTransitivityGenerator} with {@link Doubleton}s.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <C>
 *            content type; a user uses {@link Doubleton}s of {@link C} elements.
 */
public class ScopedTransitivityGeneratorDoubleton<C> extends ScopedTransitivityGenerator<Doubleton<C>, C> {
	/**
	 * Constructor.
	 * 
	 * @param compressPaths
	 *            true iff paths should be compressed
	 */
	public ScopedTransitivityGeneratorDoubleton(final boolean compressPaths) {
		super(compressPaths);
	}

	@Override
	protected Doubleton<C> createPair(final C content1, final C content2) {
		return new Doubleton<>(content1, content2);
	}

	@Override
	protected C getFirst(final Doubleton<C> pair) {
		return pair.getOneElement();
	}

	@Override
	protected C getSecond(final Doubleton<C> pair) {
		return pair.getOtherElement();
	}

	@Override
	public boolean hasContent(final Doubleton<C> pair) {
		return mContent2node.containsKey(pair.getOneElement()) && mContent2node.containsKey(pair.getOtherElement());
	}
}
