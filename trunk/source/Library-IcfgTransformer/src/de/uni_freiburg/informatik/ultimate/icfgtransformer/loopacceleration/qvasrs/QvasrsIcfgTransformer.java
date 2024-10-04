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

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformationBacktranslator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrUtils;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.Backbone;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.Loop;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.LoopDetector;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Class for applying the qvasr loop summarization technique in conjunction with IcfgTransformation.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 *
 * @param <INLOC>
 *            in locations
 * @param <OUTLOC>
 *            out locations
 */
public class QvasrsIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<OUTLOC> mResult;

	private final IcfgTransformationBacktranslator mBackTranslationTracker;

	/**
	 * Construct a new qvasr loop icfgtransformer.
	 *
	 * @param logger
	 *            An {@link ILogger}
	 * @param originalIcfg
	 *            The original {@link IIcfg}
	 * @param outLocationClass
	 *            outlocation class
	 * @param funLocFac
	 *            A {@link ILocationFactory}
	 * @param newIcfgIdentifier
	 *            New name for the transformed {@link IIcfg}
	 * @param backtranslationTracker
	 *            An {@link IcfgTransformationBacktranslator}
	 * @param services
	 *            An {@link IUltimateServiceProvider}
	 */
	public QvasrsIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IcfgTransformationBacktranslator backtranslationTracker, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mBackTranslationTracker = backtranslationTracker;
		mResult = transform(originalIcfg, funLocFac, backtranslationTracker, outLocationClass, newIcfgIdentifier,
				transformer);
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IcfgTransformationBacktranslator backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer) {
		transformer.preprocessIcfg(originalIcfg);
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mLogger, funLocFac,
				backtranslationTracker, transformer, originalIcfg, resultIcfg);
		processLocations(originalIcfg, originalIcfg.getInitialNodes(), lst, funLocFac);
		lst.finish();
		return resultIcfg;
	}

	private void processLocations(final IIcfg<INLOC> originalIcfg, final Set<INLOC> init,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst, final ILocationFactory<INLOC, OUTLOC> funLocFac) {

		final Set<INLOC> loopHeads = originalIcfg.getLoopLocations();
		final Map<INLOC, IntVasrsAbstraction> qvasrsAbstractions = new HashMap<>();

		final LoopDetector<INLOC> detecWerner =
				new LoopDetector<>(mLogger, originalIcfg, originalIcfg.getLoopLocations(), mScript, mServices, 0);

		final Map<IcfgLocation, Loop> loopWer = detecWerner.getLoopBodies();
		final Map<INLOC, UnmodifiableTransFormula> loopsWithLoopHead = new HashMap<>();

		for (final Entry<IcfgLocation, Loop> loopMap : loopWer.entrySet()) {
			final Deque<Backbone> distinctLoopPaths = loopMap.getValue().getBackbones();
			final UnmodifiableTransFormula[] distinctPathsFormulas =
					new UnmodifiableTransFormula[distinctLoopPaths.size()];
			int i = 0;
			for (final Backbone distinctLoopPath : distinctLoopPaths) {
				distinctPathsFormulas[i] = (UnmodifiableTransFormula) distinctLoopPath.getFormula();
				i++;
			}
			final UnmodifiableTransFormula loopDisjunction =
					TransFormulaUtils.parallelComposition(mLogger, mServices, mScript, null, false,
							false, distinctPathsFormulas);
			mLogger.warn(loopDisjunction.toStringDirect());
			loopsWithLoopHead.put((INLOC) loopMap.getKey(), loopDisjunction);
		}

		final QvasrsSummarizer qvasrsSummarizer = new QvasrsSummarizer(mLogger, mServices, mScript);
		for (final Entry<INLOC, UnmodifiableTransFormula> loopMap : loopsWithLoopHead.entrySet()) {
			qvasrsAbstractions.put(loopMap.getKey(), QvasrUtils.qvasrsAbstactionToIntVasrsAbstraction(mScript,
					qvasrsSummarizer.computeQvasrsAbstraction(loopMap.getValue(), true)));
		}

		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(init);

		// we need to create new return transitions after new call transitions have been created
		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		while (iter.hasNext()) {
			final INLOC oldSource = iter.next();
			OUTLOC newSource;
			if (loopHeads.contains(oldSource)) {
				int i = 0;
				final IntVasrsAbstraction abstraction = qvasrsAbstractions.get(oldSource);
				final Map<Term, OUTLOC> qvasrsStateToLoc = new HashMap<>();
				for (final Term state : abstraction.getStates()) {
					final StringDebugIdentifier id = new StringDebugIdentifier("QVASRSnode " + Integer.toString(i));
					@SuppressWarnings("unchecked")
					final OUTLOC newLoc = (OUTLOC) new IcfgLocation(id, oldSource.getProcedure());
					qvasrsStateToLoc.put(state, newLoc);
					i++;
				}
				final Term[] inVarsReal =
						abstraction.getInVars().values().toArray(new Term[abstraction.getInVars().size()]);
				final Term[] outVarsReal =
						abstraction.getOutVars().values().toArray(new Term[abstraction.getOutVars().size()]);

				final Term[][] variableRelationsIn = QvasrUtils.matrixVectorMultiplicationWithVariables(mScript,
						abstraction.getSimulationMatrix(), QvasrUtils.transposeRowToColumnTermVector(inVarsReal));
				final Term[][] variableRelationsOut = QvasrUtils.matrixVectorMultiplicationWithVariables(mScript,
						abstraction.getSimulationMatrix(), QvasrUtils.transposeRowToColumnTermVector(outVarsReal));

				for (final Triple<Term, Pair<Integer[], Integer[]>, Term> transformer : abstraction.getTransitions()) {
					final OUTLOC newStart = qvasrsStateToLoc.get(transformer.getFirst());
					final OUTLOC newTarget = qvasrsStateToLoc.get(transformer.getThird());
					for (int dimension = 0; dimension < transformer.getSecond().getFirst().length; dimension++) {
						final Set<Term> dimensionConjunction = new HashSet<>();
						final Integer dimensionReset = transformer.getSecond().getFirst()[dimension];
						final Integer dimensionAddition = transformer.getSecond().getSecond()[dimension];
						if (dimensionReset == 0) {
							final Term equality =
									SmtUtils.binaryEquality(mScript.getScript(), variableRelationsOut[dimension][0],
											mScript.getScript().numeral(dimensionAddition.toString()));
							dimensionConjunction.add(equality);
						} else {
							final Term addition =
									SmtUtils.sum(mScript.getScript(), "+", variableRelationsIn[dimension][0],
											mScript.getScript().decimal(dimensionAddition.toString()));
							final Term equality = SmtUtils.binaryEquality(mScript.getScript(),
									variableRelationsOut[dimension][0], addition);
							dimensionConjunction.add(equality);
						}
						Term transitionConjunction = SmtUtils.and(mScript.getScript(), dimensionConjunction);
						transitionConjunction =
								SmtUtils.and(mScript.getScript(), transitionConjunction, transformer.getThird());
						final Map<IProgramVar, TermVariable> freshInvars = new HashMap<>();
						final Map<IProgramVar, TermVariable> freshOutvars = new HashMap<>();
						final Map<Term, Term> freshVars = new HashMap<>();
						for (final Entry<IProgramVar, TermVariable> oldInvars : abstraction.getInVars().entrySet()) {
							final TermVariable freshVar = mScript.constructFreshCopy(oldInvars.getValue());
							freshInvars.put(oldInvars.getKey(), freshVar);
							freshVars.put(oldInvars.getValue(), freshVar);
						}
						for (final Entry<IProgramVar, TermVariable> oldOutvars : abstraction.getOutVars().entrySet()) {
							final TermVariable freshVar = mScript.constructFreshCopy(oldOutvars.getValue());
							freshOutvars.put(oldOutvars.getKey(), freshVar);
							freshVars.put(oldOutvars.getValue(), freshVar);
						}
						final TransFormulaBuilder tfb =
								new TransFormulaBuilder(freshInvars, freshOutvars, true, null, true, null, true);
						tfb.setFormula(Substitution.apply(mScript, freshVars, transitionConjunction));
						tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
						final UnmodifiableTransFormula transtition = tfb.finishConstruction(mScript);

						lst.createNewInternalTransition(newStart, newTarget, transtition, false);
					}
				}
				newSource = lst.createNewLocation(oldSource);
				final IcfgLocation possibleExits = loopWer.get(oldSource).getLoopExit();
				final OUTLOC newTarget = lst.createNewLocation((INLOC) possibleExits);
				final UnmodifiableTransFormula exitTranstition = QvasrUtils.buildFormula(mScript,
						abstraction.getPostState(), abstraction.getOutVars(), abstraction.getOutVars());
				lst.createNewInternalTransition(newSource, newTarget, exitTranstition, false);

				for (final Term state : abstraction.getStates()) {
					final UnmodifiableTransFormula entryTransition = QvasrUtils.buildFormula(mScript,
							abstraction.getPreState(), abstraction.getInVars(), abstraction.getInVars());
					final OUTLOC stateState = qvasrsStateToLoc.get(state);
					lst.createNewInternalTransition(newSource, stateState, entryTransition, false);
				}

				for (final Term state : abstraction.getStates()) {
					final UnmodifiableTransFormula exitTransition = QvasrUtils.buildFormula(mScript,
							abstraction.getPostState(), abstraction.getOutVars(), abstraction.getOutVars());
					final OUTLOC stateState = qvasrsStateToLoc.get(state);
					lst.createNewInternalTransition(stateState, newTarget, exitTransition, false);
				}

			} else {
				for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
					newSource = lst.createNewLocation(oldSource);
					@SuppressWarnings("unchecked")
					final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget());
					if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
						rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
					} else {
						lst.createNewTransition(newSource, newTarget, oldTransition);
					}
				}
			}

		}
		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	private UnmodifiableTransFormula edgesToFormula(final Deque<IcfgEdge> loopEdges) {
		final List<UnmodifiableTransFormula> edgeTransitions = new ArrayList<>();
		for (final IcfgEdge edge : loopEdges) {
			edgeTransitions.add(edge.getTransformula());
		}
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mScript, true, true, false,
				SimplificationTechnique.POLY_PAC, edgeTransitions);
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}