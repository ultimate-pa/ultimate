/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker plug-in.
 *
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 * Extract stem and loop (given as NestedWords) from a RCFG. Therefore - we transform the RCFG into a Büchi automaton
 * (each state is accepting) - we (try to) obtain a lasso via an emptiness check - we return this stem and loop of this
 * lasso - furthermore we have to check if the input was indeed a lasso program - therefore we construct an automaton
 * that has the shape of the found lasso and check if the language of the RCFG-Büchi-automaton is already included in
 * the lasso automaton (via constructing difference and checking emptiness).
 *
 * @author Matthias Heizmann
 */
public class LassoExtractorBuchi<LETTER extends IIcfgTransition<?>> extends AbstractLassoExtractor<LETTER> {

	private final IUltimateServiceProvider mServices;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mCfgAutomaton;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mLassoAutomaton;
	private final PredicateFactoryResultChecking mPredicateFactoryRc;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final ILogger mLogger;

	public LassoExtractorBuchi(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final ILogger logger)
			throws AutomataLibraryException {
		mServices = Objects.requireNonNull(services);
		mLogger = Objects.requireNonNull(logger);
		mCsToolkit = Objects.requireNonNull(csToolkit);
		mPredicateFactory = Objects.requireNonNull(predicateFactory);
		mPredicateFactoryRc = new PredicateFactoryResultChecking(mPredicateFactory);
		mCfgAutomaton = constructCfgAutomaton(rootNode, mCsToolkit);
		final NestedLassoRun<LETTER, IPredicate> run =
				new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), mCfgAutomaton).getAcceptingNestedLassoRun();

		if (run == null) {
			mLassoFound = false;
			mSomeNoneForErrorReport = extractSomeNodeForErrorReport(rootNode);
		} else {
			final NestedLassoWord<LETTER> nlw = run.getNestedLassoWord();
			mLassoAutomaton = new LassoAutomatonBuilder<>(mCfgAutomaton.getVpAlphabet(), mPredicateFactoryRc,
					mPredicateFactory, nlw.getStem(), nlw.getLoop(), mServices).getResult();
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> difference =
					new BuchiDifferenceFKV<>(new AutomataLibraryServices(mServices), mPredicateFactoryRc, mCfgAutomaton,
							mLassoAutomaton).getResult();
			final boolean isEmpty = new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), difference).getResult();
			if (isEmpty) {
				mLassoFound = true;
				mHonda = extractHonda(run);
				mStem = run.getNestedLassoWord().getStem();
				mLoop = run.getNestedLassoWord().getLoop();
			} else {
				mLassoFound = false;
				mSomeNoneForErrorReport = extractSomeNodeForErrorReport(rootNode);
			}
		}
	}

	private static IcfgLocation extractSomeNodeForErrorReport(final IIcfg<?> rootNode) {
		return rootNode.getProcedureEntryNodes().entrySet().iterator().next().getValue();
	}

	private static IcfgLocation extractHonda(final NestedLassoRun<?, IPredicate> run) {
		return ((ISLPredicate) run.getLoop().getStateAtPosition(0)).getProgramPoint();
	}

	private INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>
			constructCfgAutomaton(final IIcfg<IcfgLocation> rootNode, final CfgSmtToolkit csToolkit) {
		final Collection<IcfgLocation> allNodes = new HashSet<>();
		for (final Map<DebugIdentifier, IcfgLocation> prog2pp : rootNode.getProgramPoints().values()) {
			allNodes.addAll(prog2pp.values());
		}
		return CFG2NestedWordAutomaton.constructAutomatonWithSPredicates(mServices, rootNode, mPredicateFactoryRc,
				allNodes, true, mPredicateFactory);
	}
}
