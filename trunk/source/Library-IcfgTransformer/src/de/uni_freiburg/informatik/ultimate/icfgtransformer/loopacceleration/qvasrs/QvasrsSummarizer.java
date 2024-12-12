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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.IVasr;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.Qvasr;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrAbstraction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrAbstractionJoin;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrAbstractor;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * A summarizer for {@link QvasrsAbstraction} UnmodifiableTransFormula}.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrsSummarizer {
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
	public QvasrsSummarizer(final ILogger logger, final IUltimateServiceProvider services, final ManagedScript script) {
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
	public QvasrsAbstraction computeQvasrsAbstraction(final UnmodifiableTransFormula transitionFormula,
			final boolean usedInIcfgTransformation) {
		Set<Term> disjuncts = QvasrUtils.splitDisjunction(transitionFormula.getFormula());
		final Set<Term> guards = new HashSet<>();
		for (final Term disjunct : disjuncts) {
			final UnmodifiableTransFormula disTf = QvasrUtils.buildFormula(transitionFormula, disjunct, mScript);
			guards.add(TransFormulaUtils.computeGuard(disTf, mScript, mServices).getFormula());
		}

		disjuncts = guards;
		disjuncts = QvasrUtils.checkDisjoint(disjuncts, mScript, mServices, SimplificationTechnique.SIMPLIFY_DDA);

		final Map<Term, Term> outToInMap = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> outVar : transitionFormula.getOutVars().entrySet()) {
			if (transitionFormula.getInVars().containsKey(outVar.getKey())) {
				outToInMap.put(outVar.getValue(), transitionFormula.getInVars().get(outVar.getKey()));
			} else {
				outToInMap.put(outVar.getValue(), outVar.getValue());
			}
		}

		final Set<Triple<Pair<Term, Term>, IVasr<Rational>, Rational[][]>> simulationMatrices = new HashSet<>();
		final int tfDimension = transitionFormula.getAssignedVars().size();
		final Rational[][] identityMatrix = QvasrUtils.getIdentityMatrix(tfDimension);
		QvasrAbstraction bestAbstraction = new QvasrAbstraction(identityMatrix, new Qvasr());

		/*
		 * Construct formulas of the for p(x) /\ tf /\ q(x') for predicates p and q.
		 */
		for (final Term pre : disjuncts) {
			final Term preInvar = Substitution.apply(mScript, outToInMap, pre);
			for (final Term post : disjuncts) {
				final Term conjunctionPreTfPost =
						SmtUtils.and(mScript.getScript(), preInvar, transitionFormula.getFormula(), post);
				final UnmodifiableTransFormula conjunctionFormula =
						QvasrUtils.buildFormula(transitionFormula, conjunctionPreTfPost, mScript);

				final Term conjunctionDNF = SmtUtils.toDnf(mServices, mScript, conjunctionFormula.getFormula());
				final Set<Term> disjunctsAbtraction = QvasrUtils.splitDisjunction(conjunctionDNF);
				QvasrAbstraction preTfPostAbstraction = new QvasrAbstraction(identityMatrix, new Qvasr());
				for (final Term disjunct : disjunctsAbtraction) {
					mLogger.warn(disjunct.toStringDirect());
					final UnmodifiableTransFormula disjunctTf =
							QvasrUtils.buildFormula(transitionFormula, disjunct, mScript);
					final QvasrAbstraction qvasrAbstraction = QvasrAbstractor.computeAbstraction(mServices, mScript,
							disjunctTf);
					preTfPostAbstraction = QvasrAbstractionJoin.join(mScript, bestAbstraction, qvasrAbstraction)
							.getThird();
				}
				final Triple<Rational[][], Rational[][], QvasrAbstraction> abstractionWithSimulations =
						QvasrAbstractionJoin.join(mScript, bestAbstraction, preTfPostAbstraction);
				final Pair<Term, Term> prePostPair = new Pair<>(pre, post);
				simulationMatrices.add(new Triple<>(prePostPair, preTfPostAbstraction.getVasr(),
						abstractionWithSimulations.getSecond()));
				bestAbstraction = QvasrAbstractionJoin.join(mScript, bestAbstraction, preTfPostAbstraction).getThird();
			}
		}

		final Map<IProgramVar, TermVariable> inVarsReal = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVarsReal = new HashMap<>();
		for (final IProgramVar assVar : transitionFormula.getOutVars().keySet()) {
			if (transitionFormula.getInVars().containsKey(assVar)) {
				inVarsReal.put(assVar, transitionFormula.getInVars().get(assVar));
			} else if (transitionFormula.getOutVars().containsKey(assVar)) {
				inVarsReal.put(assVar, transitionFormula.getOutVars().get(assVar));
			}
			if (transitionFormula.getOutVars().containsKey(assVar)) {
				outVarsReal.put(assVar, transitionFormula.getOutVars().get(assVar));
			}
		}

		final QvasrsAbstraction qvasrsAbstraction =
				new QvasrsAbstraction(bestAbstraction, disjuncts, inVarsReal, outVarsReal);
		for (final Triple<Pair<Term, Term>, IVasr<Rational>, Rational[][]> qvasrSimulationPair : simulationMatrices) {
			final Term pre = qvasrSimulationPair.getFirst().getFirst();
			final Term post = qvasrSimulationPair.getFirst().getSecond();
			final Qvasr qvasrImage =
					QvasrAbstractionJoin.image(qvasrSimulationPair.getSecond(), qvasrSimulationPair.getThird());
			for (final Pair<Rational[], Rational[]> translatedTransformer : qvasrImage.getTransformer()) {
				final Triple<Term, Pair<Rational[], Rational[]>, Term> transition =
						new Triple<>(pre, translatedTransformer, post);
				if (checkIfTransitionIsAbsent(transition, qvasrsAbstraction)) {
					qvasrsAbstraction.addTransition(transition);
				}
			}
		}

		/*
		 * Get pre and post states when used in IcfgTransformation.
		 */
		if (usedInIcfgTransformation) {
			final UnmodifiableTransFormula guard =
					TransFormulaUtils.computeGuard(transitionFormula, mScript, mServices);
			qvasrsAbstraction.setPreState(guard.getFormula());
			final Map<Term, Term> subMap = new HashMap<>();
			for (final Entry<IProgramVar, TermVariable> invars : transitionFormula.getInVars().entrySet()) {
				if (transitionFormula.getOutVars().containsKey(invars.getKey())) {
					subMap.put(invars.getValue(), transitionFormula.getOutVars().get(invars.getKey()));
				}
			}
			final Term postLoop = Substitution.apply(mScript, subMap, guard.getFormula());
			qvasrsAbstraction.setPostState(SmtUtils.not(mScript.getScript(), postLoop));
		}
		return qvasrsAbstraction;
	}

	private final boolean checkIfTransitionIsAbsent(final Triple<Term, Pair<Rational[], Rational[]>, Term> transition,
			final QvasrsAbstraction qvasrsAbstraction) {
		boolean absent = true;
		for (final Triple<Term, Pair<Rational[], Rational[]>, Term> t : qvasrsAbstraction.getTransitions()) {
			if (QvasrUtils.checkTermEquiv(mScript, t.getFirst(), transition.getFirst())
					|| QvasrUtils.checkTermEquiv(mScript, t.getThird(), transition.getThird())) {
				for (int i = 0; i < t.getSecond().getFirst().length; i++) {
					if (transition.getSecond().getFirst()[i] != t.getSecond().getFirst()[i]) {
						break;
					}
					if (transition.getSecond().getSecond()[i] != t.getSecond().getSecond()[i]) {
						break;
					}
					absent = false;
				}
			}

		}
		return absent;
	}

	private final Term substituteVars(final Term termToBeSubbed, final Map<IProgramVar, TermVariable> toBeSubstituted) {
		final Map<TermVariable, TermVariable> sub = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> old : toBeSubstituted.entrySet()) {
			sub.put(old.getKey().getTermVariable(), old.getValue());
		}
		return Substitution.apply(mScript, sub, termToBeSubbed);
	}
}
