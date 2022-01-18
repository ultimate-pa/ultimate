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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * A summarizer for an ({@link UnmodifiableTransFormula}).
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrSummarizer {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	/**
	 * Construct a new ({@link UnmodifiableTransFormula}) summarizer based on rational vector addition systems with
	 * resets (Q-VASR)
	 *
	 * @param logger
	 *            A {@link ILogger}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param script
	 *            A {@link ManagedScript}
	 */
	public QvasrSummarizer(final ILogger logger, final IUltimateServiceProvider services, final ManagedScript script) {
		mLogger = logger;
		mScript = script;
		mServices = services;

	}

	/**
	 * Summarize a {@link UnmodifiableTransFormula} using Q-Vasr.
	 *
	 * @param transitionFormula
	 *            A {@link UnmodifiableTransFormula} representing changes to variables.
	 * @return A summary of these changes in form of a {@link UnmodifiableTransFormula}
	 */
	public UnmodifiableTransFormula summarizeLoop(final UnmodifiableTransFormula transitionFormula) {
		final Term transitionTerm = transitionFormula.getFormula();
		final Term transitionTermDnf = SmtUtils.toDnf(mServices, mScript, transitionTerm,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final int tfDimension = transitionFormula.getAssignedVars().size();
		final Rational[][] identityMatrix = QvasrUtils.getIdentityMatrix(tfDimension);
		QvasrAbstraction bestAbstraction = new QvasrAbstraction(identityMatrix, new Qvasr());

		final QvasrAbstractor qvasrAbstractor = new QvasrAbstractor(mScript, mLogger, mServices);

		final List<Term> disjuncts = QvasrUtils.splitDisjunction(transitionTermDnf);

		for (final Term disjunct : disjuncts) {
			final QvasrAbstraction qvasrAbstraction = qvasrAbstractor.computeAbstraction(disjunct, transitionFormula);
			bestAbstraction = QvasrAbstractionJoin.join(mScript, bestAbstraction, qvasrAbstraction);
		}
		/**
		 * TODO Error because something isn't integral?
		 */
		final UnmodifiableTransFormula qvasrAsTf =
				qvasrAbstractionToFormula(mScript, bestAbstraction, transitionFormula);
		return transitionFormula;
	}

	/**
	 * Compute a {@link UnmodifiableTransFormula} as loop summary. This version can deal with branching loops.
	 *
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param qvasrAbstraction
	 *            A {@link QvasrAbstraction} whose reachability relation we want to compute.
	 * @param tf
	 *            The original {@link UnmodifiableTransFormula} of the loop.
	 * @return An overapproximative loop summary computed from a qvasr abstraction.
	 */
	public static UnmodifiableTransFormula qvasrAbstractionToFormula(final ManagedScript script,
			final QvasrAbstraction qvasrAbstraction, final UnmodifiableTransFormula tf) {

		final Term[] inVars = tf.getInVars().values().toArray(new Term[tf.getInVars().size()]);
		final Term[] outVars = tf.getOutVars().values().toArray(new Term[tf.getOutVars().size()]);
		final IProgramVar[] inVarsPv = tf.getInVars().keySet().toArray(new IProgramVar[tf.getInVars().size()]);
		final IProgramVar[] outVarsPv = tf.getOutVars().keySet().toArray(new IProgramVar[tf.getOutVars().size()]);

		final Term[] inVarsReal = tf.getInVars().values().toArray(new Term[tf.getInVars().size()]);
		final Term[] outVarsReal = tf.getOutVars().values().toArray(new Term[tf.getOutVars().size()]);

		final Map<IProgramVar, TermVariable> newInvars = new HashMap<>();
		final Map<IProgramVar, TermVariable> newOutvars = new HashMap<>();

		for (int i = 0; i < inVars.length; i++) {
			final TermVariable tv =
					script.constructFreshTermVariable(inVars[i].toString() + "_real", SmtSortUtils.getRealSort(script));
			inVarsReal[i] = tv;
			newInvars.put(inVarsPv[i], tv);
		}

		for (int i = 0; i < outVars.length; i++) {
			final TermVariable tv = script.constructFreshTermVariable(outVars[i].toString() + "_real_Primed",
					SmtSortUtils.getRealSort(script));
			outVarsReal[i] = tv;
			newOutvars.put(outVarsPv[i], tv);
		}

		final Term[][] variableRelationsIn = QvasrUtils.matrixVectorMultiplicationWithVariables(script,
				qvasrAbstraction.getSimulationMatrix(), QvasrUtils.transposeRowToColumnTermVector(inVarsReal));
		final Term[][] variableRelationsOut = QvasrUtils.matrixVectorMultiplicationWithVariables(script,
				qvasrAbstraction.getSimulationMatrix(), QvasrUtils.transposeRowToColumnTermVector(outVarsReal));

		final List<Term> qvasrDimensionConjunction = new ArrayList<>();

		final Map<Integer, TermVariable> kToTransformer = new HashMap<>();

		for (int dimension = 0; dimension < qvasrAbstraction.getQvasr().getDimension(); dimension++) {
			final Set<Term> dimensionDisjunction = new HashSet<>();
			Term dimensionSumTerm = variableRelationsIn[dimension][0];
			boolean incrementFlag = false;
			int transformerId = 0;
			for (final Pair<Rational[], Rational[]> transformer : qvasrAbstraction.getQvasr().getQvasrTransformer()) {
				final Rational dimensionReset = transformer.getFirst()[dimension];
				final Rational dimensionAddition = transformer.getSecond()[dimension];
				if (dimensionReset == Rational.ZERO) {
					final Term equality =
							SmtUtils.binaryEquality(script.getScript(), variableRelationsOut[dimension][0],
									dimensionAddition.toTerm(SmtSortUtils.getRealSort(script)));
					dimensionDisjunction.add(equality);

				} else {
					TermVariable k;
					if (kToTransformer.containsKey(transformerId)) {
						k = kToTransformer.get(transformerId);
					} else {
						k = script.constructFreshTermVariable("k", SmtSortUtils.getRealSort(script));
						kToTransformer.put(transformerId, k);
					}
					final Term quantifiedAddition =
							SmtUtils.mul(script.getScript(), transformer.getSecond()[dimension], k);
					dimensionSumTerm = SmtUtils.sum(script.getScript(), "+", dimensionSumTerm, quantifiedAddition);
					incrementFlag = true;
				}
				transformerId++;
			}
			if (incrementFlag) {
				final Term equality = SmtUtils.binaryEquality(script.getScript(), variableRelationsOut[dimension][0],
						dimensionSumTerm);
				dimensionDisjunction.add(equality);
			}
			qvasrDimensionConjunction.add(SmtUtils.or(script.getScript(), dimensionDisjunction));
		}

		Term loopSummary = SmtUtils.and(script.getScript(), qvasrDimensionConjunction);
		loopSummary = SmtUtils.quantifier(script.getScript(), QuantifiedFormula.EXISTS, kToTransformer.values(),
				SmtUtils.and(script.getScript(), loopSummary));
		/*
		 * Error because of non Theory constants?
		 */
		final TransFormulaBuilder tfb = new TransFormulaBuilder(newInvars, newOutvars, true, null, true, null, true);
		tfb.setFormula(loopSummary);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(script);
	}

	/**
	 * Construct a {@link UnmodifiableTransFormula} as loop summary, tailored to the method of splitting loop formulas
	 * into disjuncts, which then creates at maximum one {@link QvasrAbstraction}. Meaning in the original loop
	 * transformula there is no branching.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param qvasrAbstraction
	 *            A {@link QvasrAbstraction} whose reachability relation we want to compute.
	 * @param tf
	 *            The original {@link UnmodifiableTransFormula} of the loop.
	 * @return An overapproximative loop summary computed from a qvasr abstraction.
	 */
	public static UnmodifiableTransFormula qvasrAbstractionToFormulaMetaTrace(final ManagedScript script,
			final QvasrAbstraction qvasrAbstraction, final UnmodifiableTransFormula tf) {

		final Term[] inVars = tf.getInVars().values().toArray(new Term[tf.getInVars().size()]);
		final Term[] outVars = tf.getOutVars().values().toArray(new Term[tf.getOutVars().size()]);
		final IProgramVar[] inVarsPv = tf.getInVars().keySet().toArray(new IProgramVar[tf.getInVars().size()]);
		final IProgramVar[] outVarsPv = tf.getOutVars().keySet().toArray(new IProgramVar[tf.getOutVars().size()]);

		final Term[] inVarsReal = tf.getInVars().values().toArray(new Term[tf.getInVars().size()]);
		final Term[] outVarsReal = tf.getOutVars().values().toArray(new Term[tf.getOutVars().size()]);

		final Map<IProgramVar, TermVariable> newInvars = new HashMap<>();
		final Map<IProgramVar, TermVariable> newOutvars = new HashMap<>();

		for (int i = 0; i < inVars.length; i++) {
			final TermVariable tv =
					script.constructFreshTermVariable(inVars[i].toString() + "_real", SmtSortUtils.getRealSort(script));
			inVarsReal[i] = tv;
			newInvars.put(inVarsPv[i], tv);
		}

		for (int i = 0; i < outVars.length; i++) {
			final TermVariable tv = script.constructFreshTermVariable(outVars[i].toString() + "_real_Primed",
					SmtSortUtils.getRealSort(script));
			outVarsReal[i] = tv;
			newOutvars.put(outVarsPv[i], tv);
		}

		final Term[][] variableRelationsIn = QvasrUtils.matrixVectorMultiplicationWithVariables(script,
				qvasrAbstraction.getSimulationMatrix(), QvasrUtils.transposeRowToColumnTermVector(inVarsReal));
		final Term[][] variableRelationsOut = QvasrUtils.matrixVectorMultiplicationWithVariables(script,
				qvasrAbstraction.getSimulationMatrix(), QvasrUtils.transposeRowToColumnTermVector(outVarsReal));

		final List<Term> qvasrDisjunction = new ArrayList<>();
		for (final Pair<Rational[], Rational[]> transformer : qvasrAbstraction.getQvasr().getQvasrTransformer()) {
			final TermVariable k = script.constructFreshTermVariable("k", SmtSortUtils.getRealSort(script));
			final List<Term> qvasrConjuncts = new ArrayList<>();
			for (int i = 0; i < qvasrAbstraction.getQvasr().getDimension(); i++) {
				final Term reset =
						SmtUtils.mul(script.getScript(), transformer.getFirst()[i], variableRelationsIn[i][0]);
				final Term quantifiedAddition = SmtUtils.mul(script.getScript(), transformer.getSecond()[i], k);
				final Term addition = SmtUtils.sum(script.getScript(), "+", reset, quantifiedAddition);
				final Term equality = SmtUtils.binaryEquality(script.getScript(), variableRelationsOut[i][0], addition);
				qvasrConjuncts.add(equality);
			}
			final Term qvasrConjunctionQuantified = SmtUtils.quantifier(script.getScript(), QuantifiedFormula.EXISTS,
					Arrays.asList(k), SmtUtils.and(script.getScript(), qvasrConjuncts));
			qvasrDisjunction.add(qvasrConjunctionQuantified);
		}
		final Term loopSummary = SmtUtils.or(script.getScript(), qvasrDisjunction);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(newInvars, newOutvars, true, null, true, null, true);
		tfb.setFormula(loopSummary);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(script);
	}
}
