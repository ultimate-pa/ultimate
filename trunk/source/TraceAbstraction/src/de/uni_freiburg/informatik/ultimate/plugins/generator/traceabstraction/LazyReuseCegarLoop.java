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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

/**
 * TODO:
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class LazyReuseCegarLoop<LETTER extends IIcfgTransition<?>> extends ReuseCegarLoop<LETTER> {

	private List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> mReuseAutomata;

	private Boolean mIsCounterexampleAccepted = false;
	// Should be dereferenced only if mIsCounterexampleAccepted is true
	private INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mAutomatonAcceptingCounterexample;

	public LazyReuseCegarLoop(final String name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final List<AbstractInterpolantAutomaton<LETTER>> floydHoareAutomataFromOtherLocations,
			final List<NestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFiles) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services, storage, floydHoareAutomataFromOtherLocations, rawFloydHoareAutomataFromFiles);
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();
		mReuseAutomata = new ArrayList<>();
		mReuseAutomata.addAll(mFloydHoareAutomataFromOtherErrorLocations);
		mFloydHoareAutomataFromFile.stream().map(a -> a.getAutomaton()).forEach(mReuseAutomata::add);
	}

	@Override
	protected LBool isCounterexampleFeasible() throws AutomataOperationCanceledException {
		mReuseStats.continueTime();
		mIsCounterexampleAccepted = false;
		for (int i = 0; i < mReuseAutomata.size(); i++) {
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> reuseAut = mReuseAutomata.get(i);
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
					mIsCounterexampleAccepted = true;
					mAutomatonAcceptingCounterexample = reuseAut;
					final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> removed =
							mReuseAutomata.remove(i);
					assert removed.equals(reuseAut);
					mLogger.info("Cex is accepted by automaton number " + i + " in the current list.");
					mReuseStats.stopTime();

					return LBool.UNSAT;
				}
			} catch (final AutomataLibraryException e) {
				mLogger.warn("Acceptance check of counterexample in automaton " + i
						+ " failed. Proceeding with a non-reuse iteration");
				break;
			}
		}
		mReuseStats.stopTime();
		mReuseStats.announceNextNonreuseIteration();
		// None of the preexisting automata accepts the counterexample - make a non-reuse iteration
		return super.isCounterexampleFeasible();
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		if (!mIsCounterexampleAccepted) {
			super.constructInterpolantAutomaton();
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		if (mIsCounterexampleAccepted) {
			mReuseStats.continueTime();
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> reuseAut =
					mAutomatonAcceptingCounterexample;
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
