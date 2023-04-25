package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public interface IRedGreenBlueStateFactory<CONTENT> extends IStateFactory<CONTENT> {

	/**
	 * Red content for "RGB" construction.
	 *
	 * @param content
	 *            content
	 * @return state representing the red content
	 */
	CONTENT getRedContent(final CONTENT content);

	/**
	 * Green content for "RGB" construction.
	 *
	 * @param content
	 *            content
	 * @return state representing the green content
	 */
	CONTENT getGreenContent(final CONTENT content);

	/**
	 * Green content for "RGB" construction.
	 *
	 * @param content
	 *            content
	 * @return state representing the blue content
	 */
	CONTENT getBlueContent(final CONTENT content);

	/**
	 * "colorless" content that was used to derive this "RGB" constructed content.
	 *
	 * @param content
	 *            content
	 * @return state representing the original content
	 */
	CONTENT getOriginal(final CONTENT content);

	CONTENT getRedContent(int content);
}
