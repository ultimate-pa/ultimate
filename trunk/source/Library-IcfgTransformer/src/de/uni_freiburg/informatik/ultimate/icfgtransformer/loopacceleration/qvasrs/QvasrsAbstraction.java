/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasrs;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * A class representing a rational addition vector with resets and states (Qvasrs). Consisting of a set of transitions
 * between predicates that represent program states.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrsAbstraction {
	private final Rational[][] mSimulationMatrix;
	private final Set<Term> mStates;
	private final Set<Triple<Term, Pair<Rational[], Rational[]>, Term>> mTransitions;

	/**
	 * Create a new Qvasrs-abstraction.
	 *
	 * @param simulationMatrix
	 *            The abstractions simulation matrix
	 * @param states
	 *            The set of states.
	 */
	public QvasrsAbstraction(final Rational[][] simulationMatrix, final Set<Term> states) {
		mSimulationMatrix = simulationMatrix;
		mStates = states;
		mTransitions = new HashSet<>();
	}

	/**
	 * Add a new transition between two states. This transition is modeled as a reset and addition vector pair.
	 * Representing changes to program variables and relations between program variables.
	 *
	 * @param transition
	 *            A new transition (p, [r, a], q). p, q being predicates and [r, a] is a pair of rational reset and
	 *            addition vectors.
	 */
	public void addTransition(final Triple<Term, Pair<Rational[], Rational[]>, Term> transition) {
		mTransitions.add(transition);
	}

	public Set<Term> getStates() {
		return mStates;
	}

	public Set<Triple<Term, Pair<Rational[], Rational[]>, Term>> getTransitions() {
		return mTransitions;
	}

	public Rational[][] getSimulationMatrix() {
		return mSimulationMatrix;
	}
}
