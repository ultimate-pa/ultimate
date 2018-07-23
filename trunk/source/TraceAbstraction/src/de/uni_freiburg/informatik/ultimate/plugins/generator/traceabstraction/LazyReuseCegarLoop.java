/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * TODO:
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class LazyReuseCegarLoop<LETTER extends IIcfgTransition<?>> extends ReuseCegarLoop<LETTER> {

	private List<Pair<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>, IPredicateUnifier>> mReuseAutomata;

	private boolean mReuseAutomatonAccepted = false;

	private Pair<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>, IPredicateUnifier> mAutomatonAcceptingCounterexample;

	public LazyReuseCegarLoop(final DebugIdentifier name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final List<Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier>> floydHoareAutomataFromOtherLocations,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFiles) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services, storage, floydHoareAutomataFromOtherLocations, rawFloydHoareAutomataFromFiles);
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();
		mReuseAutomata = new ArrayList<>();
		// TODO just ignore automata from other error locations for now
		// for (final Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier> pair :
		// mFloydHoareAutomataFromOtherErrorLocations) {
		// mReuseAutomata.add(new Pair<>(pair.getFirst(), pair.getSecond()));
		// }
		for (final ReuseAutomaton reAut : mFloydHoareAutomataFromFile) {
			mReuseAutomata.add(new Pair<>(reAut.getAutomaton(), reAut.getPredicateUnifier()));
		}
	}

	@Override
	protected LBool isCounterexampleFeasible() throws AutomataOperationCanceledException {
		mReuseStats.continueTime();
		mReuseAutomatonAccepted = false;
		final Iterator<Pair<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>, IPredicateUnifier>> iter =
				mReuseAutomata.iterator();
		while (iter.hasNext()) {
			final Pair<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>, IPredicateUnifier> reuseAutPair =
					iter.next();
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> reuseAut = reuseAutPair.getFirst();
			boolean cexAccepted;
			try {

				if (reuseAut instanceof AbstractInterpolantAutomaton) {
					final AbstractInterpolantAutomaton<LETTER> aiReuseAut =
							(AbstractInterpolantAutomaton<LETTER>) reuseAut;
					mReuseStats.addBeforeAcceptanceTransitions(aiReuseAut.computeNumberOfInternalTransitions());
				}

				cexAccepted = new Accepts<>(new AutomataLibraryServices(mServices), reuseAut,
						(NestedWord<LETTER>) mCounterexample.getWord(), true, true).getResult();
				if (reuseAut instanceof AbstractInterpolantAutomaton) {
					final AbstractInterpolantAutomaton<LETTER> aiReuseAut =
							(AbstractInterpolantAutomaton<LETTER>) reuseAut;
					mReuseStats.addAfterAcceptanceTransitions(aiReuseAut.computeNumberOfInternalTransitions());
				}

				if (cexAccepted) {
					mReuseAutomatonAccepted = true;
					mAutomatonAcceptingCounterexample = reuseAutPair;
					iter.remove();
					mLogger.info("Cex is accepted by reuse automaton");
					mReuseStats.stopTime();
					return LBool.UNSAT;
				}
			} catch (final AutomataLibraryException e) {
				mLogger.error("Exception during acceptance check of counterexample in reuse automaton: ", e);
			}
		}
		mReuseStats.stopTime();
		mReuseStats.announceNextNonreuseIteration();
		// None of the preexisting automata accepts the counterexample - make a non-reuse iteration
		return super.isCounterexampleFeasible();
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		if (!mReuseAutomatonAccepted) {
			super.constructInterpolantAutomaton();
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		if (mReuseAutomatonAccepted) {
			mReuseStats.continueTime();
			final Pair<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>, IPredicateUnifier> reuseAutPair =
					mAutomatonAcceptingCounterexample;
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> reuseAut = reuseAutPair.getFirst();
			if (reuseAut instanceof AbstractInterpolantAutomaton) {
				final AbstractInterpolantAutomaton<LETTER> aiReuseAut = (AbstractInterpolantAutomaton<LETTER>) reuseAut;
				mReuseStats.addBeforeDiffTransitions(aiReuseAut.computeNumberOfInternalTransitions());
			}
			final PowersetDeterminizer<LETTER, IPredicate> psd =
					new PowersetDeterminizer<>(reuseAut, true, mPredicateFactoryInterpolantAutomata);
			final boolean explointSigmaStarConcatOfIA = true;
			IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> diff;
			diff = new Difference<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, reuseAut, psd,
					explointSigmaStarConcatOfIA);

			if (reuseAut instanceof AbstractInterpolantAutomaton) {
				final AbstractInterpolantAutomaton<LETTER> aiReuseAut = (AbstractInterpolantAutomaton<LETTER>) reuseAut;
				aiReuseAut.switchToReadonlyMode();
				mReuseStats.addAfterDiffTransitions(aiReuseAut.computeNumberOfInternalTransitions());
			}

			// Check if all edges of the Floyd-Hoare automaton are indeed inductive.
			assert new InductivityCheck<>(mServices,
					new RemoveUnreachable<>(new AutomataLibraryServices(mServices), reuseAut).getResult(), false, true,
					new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult();

			dumpOrAppendAutomatonForReuseIfEnabled(reuseAut, reuseAutPair.getSecond());

			if (REMOVE_DEAD_ENDS) {
				if (mComputeHoareAnnotation) {
					final Difference<LETTER, IPredicate> difference = (Difference<LETTER, IPredicate>) diff;
					mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				diff.removeDeadEnds();
				if (mComputeHoareAnnotation) {
					mHaf.addDeadEndDoubleDeckers(diff);
				}
			}

			mAbstraction = diff.getResult();
			minimizeAbstractionIfEnabled();

			final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(mServices),
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction,
					(NestedWord<LETTER>) mCounterexample.getWord()).getResult();
			mReuseStats.stopTime();
			return !stillAccepted;

		}
		return super.refineAbstraction();
	}
}
