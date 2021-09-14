/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;


/**
 * We call two {@link Transition}s similar if they have the same letter, the
 * same predecessors and the same successors. It seems wasteful to have similar
 * transitions in a Petri net. Objects of this class can detect similar
 * transitions.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class TransitionUnifier<LETTER, PLACE> {

	final HashRelation<Integer, Transition<LETTER, PLACE>> mHash2Transitions = new HashRelation<>();

	/**
	 * @return A transition that is similar to tNew if such a transition has been
	 *         registered in the past and null otherwise.
	 */
	public Transition<LETTER, PLACE> findOrRegister(final Transition<LETTER, PLACE> tNew) {
		final int hash = computeHash(tNew);
		final Set<Transition<LETTER, PLACE>> transitionsWithSameHash = mHash2Transitions.getImage(hash);
		for (final Transition<LETTER, PLACE> tOld : transitionsWithSameHash) {
			if (areSimilar(tNew, tOld)) {
				return tOld;
			}
		}
		mHash2Transitions.addPair(hash, tNew);
		return null;
	}

	public void remove(final Transition<LETTER, PLACE> transition) {
		final int hash = computeHash(transition);
		mHash2Transitions.removePair(hash, transition);
	}

	private boolean areSimilar(final Transition<LETTER, PLACE> t1, final Transition<LETTER, PLACE> t2) {
		return t1.getSymbol().equals(t2.getSymbol()) && t1.getPredecessors().equals(t2.getPredecessors())
				&& t1.getSuccessors().equals(t2.getSuccessors());
	}

	private int computeHash(final Transition<LETTER, PLACE> t) {
		final int prime = 31;
		int result = 1;
		result = prime * result + t.getSymbol().hashCode();
		result = prime * result + t.getPredecessors().hashCode();
		result = prime * result + t.getSuccessors().hashCode();
		return result;
	}

}
