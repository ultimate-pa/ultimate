/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctConjunction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonCalculator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.ParametricOctMatrix;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Class to build FastUPR results.
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRFormulaBuilder {

	private final FastUPRUtils mUtils;
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final OctagonCalculator mCalculator;
	private final OctagonTransformer mTransformer;
	private final FastUPRTermTransformer mTermTransformer;

	/**
	 *
	 * @param utils
	 *            The {@link FastUPRUtils} used for debug output.
	 * @param mgdScript
	 *            The {@link ManagedScript} used for {@link Term}
	 *            transformation.
	 * @param calc
	 *            An {@link OctagonCalculator}
	 * @param transformer
	 *            An {@link OctagonTransformer}
	 */
	public FastUPRFormulaBuilder(FastUPRUtils utils, ManagedScript mgdScript, OctagonCalculator calc,
			OctagonTransformer transformer) {
		mUtils = utils;
		mManagedScript = mgdScript;
		mScript = mgdScript.getScript();
		mCalculator = calc;
		mTransformer = transformer;
		mTermTransformer = new FastUPRTermTransformer(mScript);
	}

	/**
	 * Builds an {@link UnmodifiableTransFormula} from a given {@link Term} and
	 * variable Mappings.
	 *
	 * @param term
	 *            The {@link Term} of the TransFormula.
	 * @param inVars
	 *            An InVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @param outVars
	 *            An OutVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @return new {@link UmodifiableTransFormula} based on the input.
	 */
	public UnmodifiableTransFormula buildTransFormula(Term term, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		final Term withoutInt = mTermTransformer.transformToInt(term);
		final ModifiableTransFormula modFormula = new ModifiableTransFormula(withoutInt);
		for (final IProgramVar p : inVars.keySet()) {
			modFormula.addInVar(p, inVars.get(p));
		}
		for (final IProgramVar p : outVars.keySet()) {
			modFormula.addOutVar(p, outVars.get(p));
		}
		return TransFormulaBuilder.constructCopy(mManagedScript, modFormula, Collections.emptySet(),
				Collections.emptySet(), Collections.emptyMap());
	}

	/**
	 * Build an Accelerated Loop Edge for Octagons that do not pass the
	 * Consistency Check.
	 *
	 * @param conjunc
	 *            The {@link OctConjunction} representing the Octagon.
	 * @param count
	 *            The last iteration where the Octagon is consistent.
	 * @param inVars
	 *            An InVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @param outVars
	 *            An OutVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @return The Disjunction representing the Loop up to it's inconsistency.
	 */
	public Term buildConsistencyResult(OctConjunction conjunc, int count, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {

		mUtils.output("Returning Consistency Result");
		final ArrayList<Term> orTerms = new ArrayList<>();
		for (int i = 0; i <= count; i++) {
			orTerms.add(mCalculator.sequentialize(conjunc, inVars, outVars, i).toTerm(mScript));
		}
		return orTerms.size() > 1 ? mScript.term("or", orTerms.toArray(new Term[0])) : orTerms.get(0);
	}

	/**
	 * Build an Accelerated Loop Edge for Octagons that are ultimately periodic
	 * without inconsistency.
	 *
	 * @param conjunc
	 *            The {@link OctConjunction} representing the Octagon.
	 * @param b
	 *            The length of the loop prefix.
	 * @param difference
	 *            The Matrix representing the difference between two loop
	 *            periods.
	 * @param inVars
	 * @param outVars
	 * @param variables
	 * @param inVars
	 *            An InVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @param outVars
	 *            An OutVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @return The Disjunction representing the Loop
	 */
	public Term buildParametricResult(OctConjunction conjunc, int b, ParametricOctMatrix difference,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			List<TermVariable> variables) {
		// R* := OR(i=0->b-1) (R^i) or EXISTS k>=0. OR(i=0->c-1)
		// (pi(k*difference + sigma(R^b)) ○ R^i

		final ArrayList<Term> firstOrTerms = new ArrayList<>();
		for (int i = 0; i < b; i++) {
			firstOrTerms.add(mCalculator.sequentialize(conjunc, inVars, outVars, i).toTerm(mScript));
		}
		final Term firstOr = firstOrTerms.size() > 1 ? mScript.term("or", firstOrTerms.toArray(new Term[0]))
				: firstOrTerms.get(0);

		final ArrayList<Term> secondOrTerms = new ArrayList<>();
		final ParametricOctMatrix parametricDiff = difference.multiplyVar("k", mManagedScript);
		for (int i = 0; i < b; i++) {
			secondOrTerms
					.add(getParametricSolutionRightSide(conjunc, b, i, parametricDiff, inVars, outVars, variables));
		}
		final Term secondOr = secondOrTerms.size() > 1 ? mScript.term("or", secondOrTerms.toArray(new Term[0]))
				: secondOrTerms.get(0);
		final Term secondOrQuantified = mScript.quantifier(QuantifiedFormula.EXISTS,
				new TermVariable[] { parametricDiff.getParametricVar() },
				mScript.term("and",
						mScript.term(">=", parametricDiff.getParametricVar(), mScript.decimal(BigDecimal.ZERO)),
						secondOr));
		final Term result = mScript.term("or", firstOr, secondOrQuantified);

		mUtils.output("Returning Parametric Result");
		return result;
	}

	private Term getParametricSolutionRightSide(OctConjunction conjunc, int b, int i,
			ParametricOctMatrix parametricDiff, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars, List<TermVariable> variables) {
		final ParametricOctMatrix rBMatrix = mTransformer
				.getMatrix(mCalculator.sequentialize(conjunc, inVars, outVars, b), variables);
		final ParametricOctMatrix completeMatrix = parametricDiff.add(rBMatrix);
		final OctConjunction firstPart = completeMatrix.toOctConjunction();
		final OctConjunction result = mCalculator.binarySequentialize(firstPart,
				mCalculator.sequentialize(conjunc, inVars, outVars, i), inVars, outVars);

		return result.toTerm(mScript);
	}

	/**
	 * Build an Accelerated Loop Edge for Octagons, where a period was found but
	 * also an inconsistency at some point.
	 *
	 * @param conjunc
	 *            The {@link OctConjunction} representing the Octagon.
	 *
	 * @param difference
	 *            The Matrix representing the difference between two loop
	 *            periods.
	 * @param b
	 *            The length of the loop prefix.
	 * @param c
	 *            The length of a loop period.
	 * @param n
	 *            The largest amount of loop calls that are consistent.
	 * @param inVars
	 *            An InVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @param outVars
	 *            An OutVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @param variables
	 *            The Ordered List of {@link TermVariable}s to build a
	 *            {@link ParametricOctMatrix}.
	 * @return The Disjunction representing the Loop.
	 */
	public Term buildPeriodicityResult(OctConjunction conjunc, ParametricOctMatrix difference, int b, int c, int n,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			List<TermVariable> variables) {
		// R* := OR(i=0->b-1) (R^i) or OR(k=0->n0-1) OR (i=0->c-1)
		// rho(k*difference + sigma(R^b)) ○ R^i

		final ArrayList<Term> firstOrTerms = new ArrayList<>();
		for (int i = 0; i < b; i++) {
			firstOrTerms.add(mCalculator.sequentialize(conjunc, inVars, outVars, i).toTerm(mScript));
		}
		final Term firstOr = firstOrTerms.size() > 1 ? mScript.term("or", firstOrTerms.toArray(new Term[0]))
				: firstOrTerms.get(0);
		final List<Term> outerOrTerms = new ArrayList<>();
		for (int k = 0; k < n; k++) {
			final List<Term> innerOrTerms = new ArrayList<>();
			for (int i = 0; i < c; i++) {
				innerOrTerms.add(getInnerOrTerm(conjunc, b, i, n, difference, inVars, outVars, variables));
			}
			final Term innerOr = innerOrTerms.size() > 1 ? mScript.term("or", innerOrTerms.toArray(new Term[0]))
					: innerOrTerms.get(0);
			outerOrTerms.add(innerOr);
		}
		final Term outerOr = outerOrTerms.size() > 1 ? mScript.term("or", outerOrTerms.toArray(new Term[0]))
				: outerOrTerms.get(0);
		final Term result = mScript.term("or", firstOr, outerOr);

		mUtils.output("Returning Periodicity Result");

		return result;
	}

	private Term getInnerOrTerm(OctConjunction conjunc, int b, int i, int n, ParametricOctMatrix difference,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			List<TermVariable> variables) {
		final ParametricOctMatrix rBMatrix = mTransformer
				.getMatrix(mCalculator.sequentialize(conjunc, inVars, outVars, b), variables);
		final ParametricOctMatrix differenceMultiplied = difference.multiplyConstant(new BigDecimal(n));
		final ParametricOctMatrix completeMatrix = differenceMultiplied.add(rBMatrix);
		final OctConjunction firstPart = completeMatrix.toOctConjunction();
		final OctConjunction result = mCalculator.binarySequentialize(firstPart,
				mCalculator.sequentialize(conjunc, inVars, outVars, i), inVars, outVars);
		return result.toTerm(mScript);
	}

	private Term getIdentityRelation(Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars) {
		final ArrayList<Term> terms = new ArrayList<>();
		for (final IProgramVar p : inVars.keySet()) {
			final TermVariable in = inVars.get(p);
			TermVariable out;
			if (outVars.containsKey(p)) {
				out = outVars.get(p);
			} else {
				out = mManagedScript.constructFreshTermVariable(in.getName() + "_out", in.getSort());
				outVars.put(p, out);
			}
			terms.add(mScript.term("=", in, out));
		}
		for (final IProgramVar p : outVars.keySet()) {
			if (!inVars.containsKey(p)) {
				final TermVariable out = outVars.get(p);
				final TermVariable in = mManagedScript.constructFreshTermVariable(out.getName() + "_in", out.getSort());
				inVars.put(p, in);
				terms.add(mScript.term("=", in, out));
			}
		}
		if (terms.isEmpty()) {
			return mScript.term("true");
		} else if (terms.size() == 1) {
			return terms.get(0);
		}
		final Term identityTerm = mScript.term("and", terms.toArray(new Term[0]));
		return identityTerm;
	}

	/**
	 * Builds a result including th exit edge
	 *
	 * @param exitEdgeFormula
	 *            The {@link UmodifiableTransFormula} of the exit edge.
	 * @param t
	 *            The term to merge with the exit edge.
	 * @param inVars
	 *            An InVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @param outVars
	 *            An OutVar-Mapping from {@link IProgramVar} to
	 *            {@link TermVariable}.
	 * @return Merged exit edge and Term t.
	 */
	public Term getExitEdgeResult(UnmodifiableTransFormula exitEdgeFormula, Term t,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars) {
		final Term identityRelation = getIdentityRelation(inVars, outVars);
		final Term loop = mScript.term("or", identityRelation, t);

		final Term exitTerm = buldExitRelation(inVars, outVars, exitEdgeFormula);

		return mScript.term("and", loop, exitTerm);
	}

	private Term buldExitRelation(Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			UnmodifiableTransFormula exitEdgeFormula) {
		Term exitTerm = exitEdgeFormula.getFormula();

		for (final Entry<IProgramVar, TermVariable> e : exitEdgeFormula.getInVars().entrySet()) {
			final TermVariable outVar = outVars.get(e.getKey());
			exitTerm = mTermTransformer.replaceVar(exitTerm, e.getValue(), outVar);
		}

		return exitTerm;
	}

}
