/*
 * Copyright (C) 2022 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.IVasrAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Interface for a vector addition system with resets and states. Can be used as rational in form of
 * {@link QvasrsAbstraction} or as integer as {@link IntVasrsAbstraction}.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            Type of Vasrs. Rational or Integer.
 */
public interface IVasrsAbstraction<S> {

	/**
	 * Add a new transition between two states. This transition is modeled as a reset and addition vector pair.
	 * Representing changes to program variables and relations between program variables.
	 *
	 * @param transition
	 *            A new transition (p, [r, a], q). p, q being predicates and [r, a] is a pair of rational reset and
	 *            addition vectors.
	 */
	void addTransition(final Triple<Term, Pair<S[], S[]>, Term> transition);

	Set<Term> getStates();

	Set<Triple<Term, Pair<S[], S[]>, Term>> getTransitions();

	S[][] getSimulationMatrix();

	Term getPreState();

	Term getPostState();

	Map<IProgramVar, TermVariable> getInVars();

	Map<IProgramVar, TermVariable> getOutVars();

	IVasrAbstraction<S> getAbstraction();

	/**
	 * Set the set of post states as a {@link Term}.
	 */
	void setPrePostStates();

	void setPostState(Term post);

	void setPreState(Term pre);

}
