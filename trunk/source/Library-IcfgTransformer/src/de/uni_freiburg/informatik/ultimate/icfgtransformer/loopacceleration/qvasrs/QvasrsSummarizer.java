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

import java.util.Collection;
import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
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
		final PredicateTransformer<Term, IPredicate, TransFormula> predTransformer =
				new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));
		final Collection<TermVariable> quantOutVars = transitionFormula.getOutVars().values();
		final Term quantifiedTransitionFormula = SmtUtils.quantifier(mScript.getScript(), QuantifiedFormula.EXISTS,
				quantOutVars, transitionFormula.getFormula());
		/*
		 * Get the topologic closure
		 */
		Term topologicClosure = PartialQuantifierElimination.eliminate(mServices, mScript, quantifiedTransitionFormula,
				SimplificationTechnique.POLY_PAC);

		topologicClosure = SmtUtils.toDnf(mServices, mScript, topologicClosure,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		Set<Term> disjuncts = QvasrUtils.splitDisjunction(topologicClosure);

		/*
		 * Get pre and post states when used in IcfgTransformation.
		 */
		if (usedInIcfgTransformation) {
			final IPredicate truePred = new BasicPredicate(0, new String[0], mScript.getScript().term("true"),
					Collections.emptySet(), mScript.getScript().term("true"));
			final Term preLoop = predTransformer.pre(truePred, transitionFormula);
			final Term postLoop = predTransformer.strongestPostcondition(truePred, transitionFormula);
			disjuncts.add(preLoop);
			disjuncts.add(postLoop);
		}

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
				final QvasrAbstraction preTfPostAbstraction =
						QvasrAbstractor.computeAbstraction(mScript, conjunctionFormula);

				final Triple<Rational[][], Rational[][], QvasrAbstraction> abstractionWithSimulations =
						QvasrAbstractionJoin.join(mScript, bestAbstraction, preTfPostAbstraction);
				final Pair<Term, Term> prePostPair = new Pair<>(pre, post);
				simulationMatrices.add(new Triple<>(prePostPair, preTfPostAbstraction.getVasr(),
						abstractionWithSimulations.getSecond()));
				bestAbstraction = abstractionWithSimulations.getThird();
			}
		}
		final QvasrsAbstraction qvasrsAbstraction =
				new QvasrsAbstraction(bestAbstraction.getSimulationMatrix(), disjuncts);
		for (final Triple<Pair<Term, Term>, IVasr<Rational>, Rational[][]> qvasrSimulationPair : simulationMatrices) {
			final Term pre = qvasrSimulationPair.getFirst().getFirst();
			final Term post = qvasrSimulationPair.getFirst().getSecond();
			final Qvasr qvasrImage =
					QvasrAbstractionJoin.image(qvasrSimulationPair.getSecond(), qvasrSimulationPair.getThird());
			for (final Pair<Rational[], Rational[]> translatedTransformer : qvasrImage.getTransformer()) {
				qvasrsAbstraction.addTransition(new Triple<>(pre, translatedTransformer, post));
			}
		}
		qvasrsAbstraction.setPrePostStates();
		return qvasrsAbstraction;
	}
}
