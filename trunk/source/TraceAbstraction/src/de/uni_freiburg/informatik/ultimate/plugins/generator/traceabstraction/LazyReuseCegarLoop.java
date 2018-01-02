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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
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
public class LazyReuseCegarLoop<LETTER extends IIcfgTransition<?>> extends BasicCegarLoop<LETTER> {

	private final List<AbstractInterpolantAutomaton<LETTER>> mFloydHoareAutomataFromOtherErrorLocations;
	private final List<NestedWordAutomaton<String, String>> mRawFloydHoareAutomataFromFiles;
	private List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> mReuseAutomata;

	private Boolean mIsCounterexampleAccepted = false; 
	private final Boolean ACCEPTS_WITH_ON_THE_FLY = true; 

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
				services, storage);
		mFloydHoareAutomataFromOtherErrorLocations = floydHoareAutomataFromOtherLocations;
		mRawFloydHoareAutomataFromFiles = rawFloydHoareAutomataFromFiles;
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();

		final List<NestedWordAutomaton<LETTER, IPredicate>> floydHoareAutomataFromFiles = AutomataReuseUtils.interpretAutomata(
				mRawFloydHoareAutomataFromFiles, (INestedWordAutomaton<LETTER, IPredicate>) mAbstraction,
				mPredicateFactoryInterpolantAutomata, mServices, mPredicateFactory, mLogger, mCsToolkit);

		mLogger.info("Reusing " + mFloydHoareAutomataFromOtherErrorLocations.size() + " Floyd-Hoare automata from previous error locations.");
		mLogger.info("Reusing " + floydHoareAutomataFromFiles.size() + " Floyd-Hoare automata from ats files.");

		mReuseAutomata = new ArrayList<>();
		mReuseAutomata.addAll(mFloydHoareAutomataFromOtherErrorLocations);
		mReuseAutomata.addAll(floydHoareAutomataFromFiles);
	}
	
	@Override
	protected LBool isCounterexampleFeasible() throws AutomataOperationCanceledException{
		mIsCounterexampleAccepted = false;
		for (int i=0; i<mReuseAutomata.size(); i++) {
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> ai = mReuseAutomata.get(i);
			boolean cexAccepted;
			try {
				if (ACCEPTS_WITH_ON_THE_FLY && ai instanceof AbstractInterpolantAutomaton<?>) {
					((AbstractInterpolantAutomaton<LETTER>)ai).switchToOnDemandConstructionMode();
				}
				cexAccepted = new Accepts<>(new AutomataLibraryServices(mServices),
						(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) ai,
						(NestedWord<LETTER>) mCounterexample.getWord(),true,true).getResult();
				if (ACCEPTS_WITH_ON_THE_FLY && ai instanceof AbstractInterpolantAutomaton<?>) {
					((AbstractInterpolantAutomaton<LETTER>)ai).switchToReadonlyMode();
				}
				if (cexAccepted) {
					mIsCounterexampleAccepted = true;
					mAutomatonAcceptingCounterexample = ai;
					final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> removed = mReuseAutomata.remove(i);
					assert (removed.equals(ai));
					mLogger.info("Cex is accepted by automaton number " + i + " in the current list.");
					return LBool.UNSAT;
				}
			} catch (AutomataLibraryException e) {
				mLogger.warn("Acceptance check of counterexample in automaton " + i + " failed. Proceeding with a non-reuse iteration");
				break;
			}
		}
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
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> ai = mAutomatonAcceptingCounterexample;
			int internalTransitionsBeforeDifference = 0;
			if (ai instanceof AbstractInterpolantAutomaton<?>) {
				internalTransitionsBeforeDifference = ((AbstractInterpolantAutomaton<LETTER>)ai).computeNumberOfInternalTransitions();
				((AbstractInterpolantAutomaton<LETTER>)ai).switchToOnDemandConstructionMode();
			}
			final PowersetDeterminizer<LETTER, IPredicate> psd = new PowersetDeterminizer<>(ai, true,
					mPredicateFactoryInterpolantAutomata);
			final boolean explointSigmaStarConcatOfIA = true;
			IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> diff;
			diff = new Difference<LETTER, IPredicate>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, ai, psd,
					explointSigmaStarConcatOfIA);
			if (ai instanceof AbstractInterpolantAutomaton<?>) {
				((AbstractInterpolantAutomaton<LETTER>)ai).switchToReadonlyMode();
				final int internalTransitionsAfterDifference = ((AbstractInterpolantAutomaton<LETTER>)ai).computeNumberOfInternalTransitions();
				mLogger.info("Floyd-Hoare automaton that acceptes counterexample had " + internalTransitionsAfterDifference
						+ " internal transitions before reuse, on-demand computation of difference added "
						+ (internalTransitionsAfterDifference - internalTransitionsBeforeDifference) + " more.");
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
			return !stillAccepted;
			
		} else {
			return super.refineAbstraction();
		}
	}

}
