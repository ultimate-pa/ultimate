/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents the transition of a program or a transition system as an SMT formula.
 *
 * The formula denotes a binary relation of this-state/next-state pairs, where we consider a state as a variable
 * assignment. Note that the this-state and the next-state may refer to different contexts, and thus range over
 * different sets of variables. For instance, in a {@code TransFormula} describing a procedure call, the this-state
 * ranges over the local variables of the caller procedure and the global variables, whereas the next-state ranges over
 * the local variables of the callee procedure and the global variables.
 *
 * <ul>
 * <li>The variables that describe the "this-state"s are given as {@link IProgramVar} stored as the keySet of the Map
 * {@code mInVars}. {@code mInVars} maps each of these variables to a corresponding {@link TermVariable} in the
 * formula.</li>
 * <li>The variables that describe the "next-state"s are given as {@link IProgramVar} stored as the keySet of the Map
 * {@code mOutVars}. {@code mOutVars} maps each of these variables to a corresponding {@link TermVariable} in the
 * formula.</li>
 * </ul>
 *
 * The transition may update the value of variables that exist both in the this-state context and in the next-state
 * context, unless they
 * <ul>
 * <li>do appear neither in {@code mInVars} nor in {@code mOutVars},</li>
 * <li>or, they appear both in {@code mInVars} and in {@code mOutVars}, with the same {@code TermVariable}.
 * </ul>
 * The names of all variables that can be updated by this transition are stored in {@code mAssignedVars} (this
 * information is obtained from {@code mInVars} and {@code mOutVars}).
 *
 * <blockquote>
 * <p>
 * <b>Example:</b> Think of a statement {@code x:=x+y}. This statement can be represented as a {@code TransFormula} with
 * the SMT formula {@code x2 = x1 + y1}, a map {@code mInVars = { x -> x1, y -> y1 }} for the this-state , and a map
 * {@code mOutVars = { x -> x2, y -> y1 }} for the next-state.
 * </p>
 * </blockquote>
 *
 * <blockquote>
 * <p>
 * <b>Example:</b> Think of a statement {@code assume x > y}. This statement can be represented as a
 * {@code TransFormula} with the SMT formula {@code x1 > y1}, a map {@code mInVars = { x -> x1, y -> y1 }} and a map
 * {@code mOutVars = { x -> x1, y -> y1 }}.
 * </p>
 * </blockquote>
 *
 *
 * <blockquote>
 * <p>
 * <b>Example:</b> Think of a statement {@code havoc x}. This statement can be represented as a {@code TransFormula}
 * with SMT formula {@code true} and either
 * <ul>
 * <li>{@code mInVars} an empty map, and {@code mOutVars} mapping {@code x} to some {@link TermVariable};</li>
 * <li>OR, {@code mInVars} mapping {@code x} to some {@link TermVariable}, and {@code mOutVars} an empty map;</li>
 * <li>OR, {@code mInVars} and {@code mOutVars} mapping {@code x} to two different {@link TermVariable}s.
 * </ul>
 * </p>
 * </blockquote>
 *
 * Additionally to {@code mInVars} and {@code mOutVars}, a {@code TransFormula} may contain auxiliary
 * {@link TermVariable}s, stored in the set {@code mAuxVars}. Such auxiliary variables can be useful to establish more
 * complex relationships between the in- and out-variables. You can think of them as implicitly existentially
 * quantified.
 *
 * <blockquote>
 * <p>
 * <b>Example:</b> Think of a {@code TransFormula} with SMT formula {@code x2 = z ∧ y2 = z}, where {@code z} is an
 * auxiliary variable, {@code mInVars} is empty, and {@code mOutVars = { x -> x2, y -> y2 }}. This describes a
 * transition that updates the values of both {@code x} and {@code y} to some nondeterministically chosen values, but
 * with the constraint that both of them have the <em>same</em> value.
 * </p>
 * </blockquote>
 *
 *
 * Formally, a TransFormula represents the set of transitions denoted by the formula φ over primed and unprimed
 * variables where φ is obtained by
 * <ul>
 * <li>first replacing for each {@code x ∈ dom(mInVars)} the TermVariable {@code mInVars(x)} in {@code mFormula} by
 * {@code x},</li>
 * <li>then replacing for each {@code x ∈ dom(mOutVars)} the TermVariable {@code mOutVars(x)} in {@code mFormula} by
 * {@code x'},</li>
 * <li>then existentially quantifying all auxiliary variables,</li>
 * <li>then adding the conjunct {@code x=x'} for each {@code x ∈ dom(mInVars) ⋂ dom(mOutVars)} such that
 * {@code mInVars(x)=mOutVars(x)},</li>
 * <li>and finally, adding the conjunct {@code x=x'} for each
 * {@code x ∈ (dom(this-state) ⋂ dom(next-state))\(dom(mInVars) ∪ dom(mOutVars))}.</li>
 * </ul>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public abstract class TransFormula implements ITransitionRelation {

	protected final Map<IProgramVar, TermVariable> mInVars;
	protected final Map<IProgramVar, TermVariable> mOutVars;
	protected final Set<TermVariable> mAuxVars;
	protected final Set<IProgramConst> mNonTheoryConsts;

	public TransFormula(final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars,
			final Set<TermVariable> auxVars, final Set<IProgramConst> nonTheoryConsts) {
		super();
		mInVars = inVars;
		mOutVars = outVars;
		mAuxVars = auxVars;
		mNonTheoryConsts = nonTheoryConsts;
	}

	public abstract Term getFormula();

	@Override
	public Map<IProgramVar, TermVariable> getInVars() {
		return Collections.unmodifiableMap(mInVars);
	}

	@Override
	public Map<IProgramVar, TermVariable> getOutVars() {
		return Collections.unmodifiableMap(mOutVars);
	}

	@Override
	public Set<IProgramConst> getNonTheoryConsts() {
		return Collections.unmodifiableSet(mNonTheoryConsts);
	}

	@Override
	public Set<TermVariable> getAuxVars() {
		return Collections.unmodifiableSet(mAuxVars);
	}

	@Override
	public boolean isHavocedOut(final IProgramVar bv) {
		final TermVariable inVar = mInVars.get(bv);
		final TermVariable outVar = mOutVars.get(bv);
		if (inVar == outVar) {
			return false;
		}
		return !Arrays.asList(getFormula().getFreeVars()).contains(outVar);
	}

	@Override
	public boolean isHavocedIn(final IProgramVar bv) {
		final TermVariable inVar = mInVars.get(bv);
		final TermVariable outVar = mOutVars.get(bv);
		if (inVar == outVar) {
			return false;
		}
		return !Arrays.asList(getFormula().getFreeVars()).contains(inVar);
	}

	public static Set<IProgramVar> collectAllProgramVars(final TransFormula tf) {
		final Set<IProgramVar> allProgramVars = new HashSet<>();
		allProgramVars.addAll(tf.getInVars().keySet());
		allProgramVars.addAll(tf.getOutVars().keySet());
		return allProgramVars;
	}
}