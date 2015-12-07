package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices;

import java.util.Comparator;

/**
 * Compares two vertices based on their progress measure as returned by
 * {@link Vertex#getPM(java.util.Set, int)} but with reverse ordering, i.e.
 * greater values come before smaller ones.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class for vertices
 * @param <STATE>
 *            State class for vertices
 */
public final class VertexPmReverseComparator<LETTER, STATE> implements Comparator<Vertex<LETTER, STATE>> {

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	@Override
	public int compare(final Vertex<LETTER, STATE> firstVertex, final Vertex<LETTER, STATE> secondVertex) {
		return Integer.compare(secondVertex.getPM(null, 0), firstVertex.getPM(null, 0));
	}

}
