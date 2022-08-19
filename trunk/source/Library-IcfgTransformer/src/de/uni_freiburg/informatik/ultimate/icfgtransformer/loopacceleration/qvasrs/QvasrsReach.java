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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Class for computing the reachability relation of a given {@link QvasrsAbstraction}.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public final class QvasrsReach {

	private QvasrsReach() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Compute the reachability relation of a given {@link QvasrsAbstraction} in form of an
	 * {@link UnmodifiableTransFormula}.
	 *
	 * @param qvasrsAbstraction
	 *            Given {@link QvasrsAbstraction} whose reachability relation it is to compute.
	 * @param script
	 *            A {@link ManagedScript}
	 * @return The {@link QvasrsAbstraction}'s reachability relation as an {@link UnmodifiableTransFormula}.
	 */
	public static UnmodifiableTransFormula reach(final QvasrsAbstraction qvasrsAbstraction,
			final ManagedScript script) {
		final List<TermVariable> parikhVars = new ArrayList<>();
		final List<TermVariable> permutationVars = new ArrayList<>();

		final Set<Triple<Term, Pair<Rational[], Rational[]>, Term>> transitions = qvasrsAbstraction.getTransitions();
		final int k = transitions.size();

		for (int i = 0; i < k; i++) {
			for (int j = 0; j < k; j++) {
				final TermVariable alpha =
						script.constructFreshTermVariable("alpha " + i + " " + j, SmtSortUtils.getIntSort(script));
				parikhVars.add(alpha);
			}
			final TermVariable sigma = script.constructFreshTermVariable("sigma " + i, SmtSortUtils.getIntSort(script));
			permutationVars.add(sigma);
		}

		/*
		 * Make sure that Sigma is a permutation.
		 */
		final Term phiPerm = computePhiPerm(permutationVars, script, k);

		/*
		 * Form a subformula for the statespace needed for flow computation.
		 */
		final List<TermVariable> stateSpaceVarsStart = new ArrayList<>();
		final List<TermVariable> stateSpaceVarsTarget = new ArrayList<>();
		for (int i = 0; i < qvasrsAbstraction.getStates().size(); i++) {
			final TermVariable s = script.constructFreshTermVariable("s " + i, SmtSortUtils.getIntSort(script));
			final TermVariable t = script.constructFreshTermVariable("s " + i, SmtSortUtils.getIntSort(script));
			stateSpaceVarsStart.add(s);
			stateSpaceVarsTarget.add(t);
		}
		final TermVariable p = script.constructFreshTermVariable("p", SmtSortUtils.getIntSort(script));
		final Term phiStates = computePhiStates(permutationVars, p, qvasrsAbstraction, k, stateSpaceVarsStart,
				stateSpaceVarsTarget, script);

		/*
		 * Last step is to compute the flow formula phiflows for which we need x^i_(p, a, q) for every transition in the
		 * qvasrs abstraction
		 */
		final List<List<TermVariable>> flows = new ArrayList<>();
		for (int i = 0; i < k; i++) {
			final List<TermVariable> flowI = new ArrayList<>();
			for (int j = 0; j < transitions.size(); j++) {
				final TermVariable xI =
						script.constructFreshTermVariable("x " + i + " " + j, SmtSortUtils.getIntSort(script));
				flowI.add(xI);
			}
			flows.add(flowI);
		}
		final Term phiFlows = computePhiFlows(permutationVars, p, qvasrsAbstraction, k, flows, script);
		return null;
	}

	/**
	 * Compute a formula phi, that expresses that permutationVars is a permutation from k to k.
	 *
	 * @param permutationVars
	 *            List of {@link TermVariable}
	 * @param script
	 *            A {@link ManagedScript}
	 * @param k
	 *            number of transitions in the {@link QvasrsAbstraction}
	 * @return A formula expressing a permutation from k to k
	 */
	private static Term computePhiPerm(final List<TermVariable> permutationVars, final ManagedScript script,
			final int k) {
		final Set<Term> phiPermConjuncts = new HashSet<>();
		final Term kTerm = script.getScript().decimal(Integer.toString(k));
		for (int i = 0; i < k; i++) {
			/*
			 * Is this a constant?
			 */
			final Term iTv = script.getScript().numeral(Integer.toString(i));
			final Set<Term> iPermConjunctions = new HashSet<>();
			final TermVariable sigma = permutationVars.get(i);
			final Term leq = SmtUtils.leq(script.getScript(), script.getScript().numeral("1"), sigma);
			final Term req = SmtUtils.leq(script.getScript(), sigma, kTerm);
			iPermConjunctions.add(req);
			iPermConjunctions.add(leq);
			for (int j = 0; j < k; j++) {
				if (i != j) {
					/*
					 * TODO: Do we need the implication i != j here?
					 */
					final Term jTv = script.getScript().numeral(Integer.toString(j));
					final TermVariable sigmaJ = permutationVars.get(j);
					/*
					 * i != j -> sigma_i != sigma_j
					 */
					final Term iNeqJ = SmtUtils.not(script.getScript(), script.getScript().term("=", iTv, jTv));
					final Term sigINeqSigJ =
							SmtUtils.not(script.getScript(), script.getScript().term("=", sigma, sigmaJ));
					iPermConjunctions.add(SmtUtils.implies(script.getScript(), iNeqJ, sigINeqSigJ));
				}
			}
			final Term iPermConjunction = SmtUtils.and(script.getScript(), iPermConjunctions);
			phiPermConjuncts.add(iPermConjunction);
		}
		return SmtUtils.and(script.getScript(), phiPermConjuncts);
	}

	/**
	 * Compute a formula modelling all possible start and target states for generalized Parikh image computation.
	 *
	 * @param permutationVars
	 *            List of {@link TermVariable}
	 * @param p
	 *            point where a reset is taken the last time.
	 * @param qvasrsAbstraction
	 *            The nondeterministic finite automaton.
	 * @param k
	 *            Number of transitions.
	 * @param stateSpaceVarsStart
	 *            List of states that can act as starting point for a flow.
	 * @param stateSpaceVarsTarget
	 *            List of states that can act as target (sink) for a flow.
	 * @param script
	 *            A {@link ManagedScript}
	 * @return A formula modelling states.
	 */
	private static Term computePhiStates(final List<TermVariable> permutationVars, final TermVariable p,
			final QvasrsAbstraction qvasrsAbstraction, final int k, final List<TermVariable> stateSpaceVarsStart,
			final List<TermVariable> stateSpaceVarsTarget, final ManagedScript script) {

		final List<TermVariable> transitions = new ArrayList<>();
		for (int i = 0; i < qvasrsAbstraction.getTransitions().size(); i++) {
			final TermVariable transition =
					script.constructFreshTermVariable("a " + i, SmtSortUtils.getIntSort(script));
			transitions.add(transition);
		}

		/*
		 * TODO: Start with i = 1 -> not sure how to encode s_0 = q_0 ?
		 */
		final List<Term> phiStatesConjuncts = new ArrayList<>();
		for (int i = 1; i < k; i++) {
			final Term iTv = script.getScript().numeral(Integer.toString(i));
			final Term iLeqP = SmtUtils.leq(script.getScript(), iTv, p);
			final Term sPrevEqTPrev = SmtUtils.binaryBooleanEquality(script.getScript(), stateSpaceVarsStart.get(i - 1),
					stateSpaceVarsTarget.get(i - 1));
			final Term tPrevEqS = SmtUtils.binaryBooleanEquality(script.getScript(), stateSpaceVarsTarget.get(i - 1),
					stateSpaceVarsStart.get(i));
			final Term lhs = SmtUtils.implies(script.getScript(), iLeqP,
					SmtUtils.and(script.getScript(), sPrevEqTPrev, tPrevEqS));

			final Term pLessI = SmtUtils.less(script.getScript(), p, iTv);
			final Term rhs = SmtUtils.implies(script.getScript(), pLessI, transitions.get(i));
			phiStatesConjuncts.add(SmtUtils.and(script.getScript(), lhs, rhs));
		}
		return SmtUtils.and(script.getScript(), phiStatesConjuncts);
	}

	/**
	 * Compute a formula for flows in a {@link QvasrsAbstraction}.
	 *
	 * @param permutationVars
	 * @param p
	 * @param qvasrsAbstraction
	 * @param k
	 * @param flows
	 * @param script
	 * @return
	 */
	private static Term computePhiFlows(final List<TermVariable> permutationVars, final TermVariable p,
			final QvasrsAbstraction qvasrsAbstraction, final int k, final List<List<TermVariable>> flows,
			final ManagedScript script) {

		final List<Term> lhs = new ArrayList<>();
		for (int i = 0; i < k; i++) {
			final Term iTv = script.getScript().numeral(Integer.toString(i));
			final Term iLessP = SmtUtils.less(script.getScript(), iTv, p);
			final List<TermVariable> flowsI = flows.get(i);
			Term sumFlowsZero;
			if (flowsI.size() > 1) {
				sumFlowsZero = SmtUtils.sum(script.getScript(), "+", flowsI.toArray(new TermVariable[flowsI.size()]));
			} else {
				sumFlowsZero = flowsI.get(0);
			}
			sumFlowsZero = script.getScript().term("=", sumFlowsZero, script.getScript().numeral("0"));
			final Term lhsImplication = SmtUtils.implies(script.getScript(), iLessP, sumFlowsZero);
			lhs.add(lhsImplication);
		}

		final Set<Triple<Term, Pair<Rational[], Rational[]>, Term>> transitions = qvasrsAbstraction.getTransitions();
		final List<Term> rhs = new ArrayList<>();
		for (int i = 0; i < k; i++) {
			final Term iTv = script.getScript().numeral(Integer.toString(i));
			final Term iLeqP = SmtUtils.leq(script.getScript(), p, iTv);
			final List<Term> rhsConjuncts = new ArrayList<>();
			for (int j = 1; j < i; j++) {
				final List<Term> transitionConjunction = new ArrayList<Term>();
				for (final Triple<Term, Pair<Rational[], Rational[]>, Term> transition : transitions) {
					/*
					 * TODO this a is wrong we need the corresponding coded a.
					 */
					final TermVariable a = script.constructFreshTermVariable("a", SmtSortUtils.getIntSort(script));
					final Term aEqualsSigma = script.getScript().term("=", a, permutationVars.get(j));
					/*
					 * TODO again use better encoding
					 */
					final Term transitionVarEqZero = script.getScript().term("=", flows.get(i).get(j));
					transitionConjunction.add(SmtUtils.implies(script.getScript(), aEqualsSigma, transitionVarEqZero));
					rhsConjuncts.add(transitionVarEqZero);
				}
			}
			rhs.add(SmtUtils.implies(script.getScript(), iLeqP, SmtUtils.and(script.getScript(), rhsConjuncts)));
		}
		return SmtUtils.and(script.getScript(), SmtUtils.and(script.getScript(), lhs),
				SmtUtils.and(script.getScript(), rhs));
	}

}
