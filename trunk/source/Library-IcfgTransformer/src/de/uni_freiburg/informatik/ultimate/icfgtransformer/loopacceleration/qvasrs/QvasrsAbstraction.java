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
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * A class representing a rational addition vector with resets and states (Qvasrs). Consisting of a set of transitions
 * between predicates that represent program states.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrsAbstraction implements IVasrsAbstraction<Rational> {
	private final QvasrAbstraction mQvasrAbstraction;
	private final Rational[][] mSimulationMatrix;
	private final Set<Term> mStates;
	private final Set<Triple<Term, Pair<Rational[], Rational[]>, Term>> mTransitions;
	private Term mPreCon;
	private Term mPostCon;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;

	/**
	 * Create a new Qvasrs-abstraction.
	 *
	 * @param simulationMatrix
	 *            The abstractions simulation matrix
	 * @param states
	 *            The set of states.
	 *
	 * @param abstraction
	 *            A {@link QvasrAbstraction} used for computing states and transitions.
	 * @param states
	 *            Set of control states in form of {@link Term}
	 * @param inVars
	 *            Map of invariables.
	 * @param outVars
	 *            Map of outvariables.
	 */
	public QvasrsAbstraction(final QvasrAbstraction abstraction, final Set<Term> states,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		mQvasrAbstraction = abstraction;
		mSimulationMatrix = abstraction.getSimulationMatrix();
		mStates = states;
		mTransitions = new HashSet<>();
		mPreCon = null;
		mPostCon = null;
		mInVars = inVars;
		mOutVars = outVars;
	}

	/**
	 * Add a new transition between two states. This transition is modeled as a reset and addition vector pair.
	 * Representing changes to program variables and relations between program variables.
	 *
	 * @param transition
	 *            A new transition (p, [r, a], q). p, q being predicates and [r, a] is a pair of rational reset and
	 *            addition vectors.
	 */
	@Override
	public void addTransition(final Triple<Term, Pair<Rational[], Rational[]>, Term> transition) {
		mTransitions.add(transition);
	}

	@Override
	public QvasrAbstraction getAbstraction() {
		return mQvasrAbstraction;
	}

	@Override
	public Set<Term> getStates() {
		return mStates;
	}

	@Override
	public Set<Triple<Term, Pair<Rational[], Rational[]>, Term>> getTransitions() {
		return mTransitions;
	}

	@Override
	public Rational[][] getSimulationMatrix() {
		return mSimulationMatrix;
	}

	@Override
	public Term getPreState() {
		return mPreCon;
	}

	@Override
	public Term getPostState() {
		return mPostCon;
	}

	@Override
	public void setPreState(final Term pre) {
		mPreCon = pre;
	}

	@Override
	public void setPostState(final Term post) {
		mPostCon = post;
	}

	@Override
	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	@Override
	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}

	@Override
	public void setPrePostStates() {
		final Set<Term> possiblePreStates = new HashSet<>(mStates);
		final Set<Term> possiblePostStates = new HashSet<>(mStates);
		for (final Triple<Term, Pair<Rational[], Rational[]>, Term> transition : mTransitions) {
			if (transition.getFirst() != transition.getThird()) {
				possiblePreStates.remove(transition.getFirst());
				possiblePostStates.remove(transition.getThird());
			}
		}
		mPreCon = possiblePreStates.toArray(new Term[1])[0];
		mPostCon = possiblePostStates.toArray(new Term[1])[0];
	}
}
