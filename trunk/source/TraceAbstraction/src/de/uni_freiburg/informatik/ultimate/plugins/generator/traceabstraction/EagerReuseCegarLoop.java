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

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
 * Subclass of {@link BasicCegarLoop} in which we initially subtract from the abstraction a set of given Floyd-Hoare
 * automata.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class EagerReuseCegarLoop<LETTER extends IIcfgTransition<?>> extends ReuseCegarLoop<LETTER> {

	private enum MinimizeInitially {
		NEVER, AFTER_EACH_DIFFERENCE, ONCE_AT_END
	}

	private static final MinimizeInitially mMinimize = MinimizeInitially.AFTER_EACH_DIFFERENCE;

	/**
	 * The following can be costly. Enable only for debugging or analyzing our algorithm
	 */
	private static final boolean IDENTIFY_USELESS_FLOYDHOARE_AUTOMATA = false;

	// TODO can this method be removed?
	public EagerReuseCegarLoop(final DebugIdentifier name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final List<Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier>> floydHoareAutomataFromOtherLocations,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services, storage, floydHoareAutomataFromOtherLocations, rawFloydHoareAutomataFromFile);
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();

		mReuseStats.continueTime();

		int autIdx = 0;
		// TODO: just ignore reuse automat from other error locs for now
		// for (final Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier> aut :
		// mFloydHoareAutomataFromOtherErrorLocations) {
		// computeDifferenceForReuseAutomaton(autIdx, aut.getFirst(), aut.getSecond());
		// ++autIdx;
		// }

		for (final ReuseAutomaton aut : mFloydHoareAutomataFromFile) {
			computeDifferenceForReuseAutomaton(autIdx, aut.getAutomaton(), aut.getPredicateUnifier());
			++autIdx;
		}

		if (mMinimize == MinimizeInitially.ONCE_AT_END) {
			minimizeAbstractionIfEnabled();
		}

		mReuseStats.stopTime();
	}

	private void computeDifferenceForReuseAutomaton(final int iteration,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> reuseAut,
			final IPredicateUnifier predicateUnifier)
			throws AutomataLibraryException, AutomataOperationCanceledException, AssertionError {
		final int oneBasedi = iteration + 1;

		if (mPref.dumpAutomata()) {
			writeAutomatonToFile(reuseAut, "ReusedAutomata" + oneBasedi);
		}

		if (reuseAut instanceof AbstractInterpolantAutomaton) {
			final AbstractInterpolantAutomaton<LETTER> aiReuseAut = (AbstractInterpolantAutomaton<LETTER>) reuseAut;
			mReuseStats.addBeforeDiffTransitions(aiReuseAut.computeNumberOfInternalTransitions());
		}

		final PowersetDeterminizer<LETTER, IPredicate> psd =
				new PowersetDeterminizer<>(reuseAut, true, mPredicateFactoryInterpolantAutomata);
		final boolean explointSigmaStarConcatOfIA = true;
		final IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> diff =
				new Difference<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
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

		if (mPref.dumpAutomata()) {
			final String filename = "DiffAfterEagerReuse" + oneBasedi;
			writeAutomatonToFile(diff.getResult(), filename);
		}

		dumpOrAppendAutomatonForReuseIfEnabled(reuseAut, predicateUnifier);

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

		if (IDENTIFY_USELESS_FLOYDHOARE_AUTOMATA) {
			final AutomataLibraryServices als = new AutomataLibraryServices(mServices);
			final Boolean noTraceExcluded = new IsIncluded<>(als, mPredicateFactoryResultChecking,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, diff.getResult())
							.getResult();
			if (noTraceExcluded) {
				mLogger.warn("Floyd-Hoare automaton" + iteration
						+ " did not remove an error trace from abstraction and was hence useless for this error location.");
			} else {
				mLogger.info("Floyd-Hoare automaton" + iteration
						+ " removed at least one error trace from the abstraction.");
			}

		}

		mAbstraction = diff.getResult();

		if (mAbstraction.size() == 0) {
			// stop to compute differences if abstraction is already empty
			return;
		}

		if (mMinimize == MinimizeInitially.AFTER_EACH_DIFFERENCE) {
			minimizeAbstractionIfEnabled();
		}
	}

}
