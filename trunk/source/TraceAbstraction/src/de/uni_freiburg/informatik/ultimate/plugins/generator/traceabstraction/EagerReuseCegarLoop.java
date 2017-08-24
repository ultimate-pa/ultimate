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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
 * Subclass of {@link BasicCegarLoop} in which we initially subtract from the
 * abstraction a set of given Floyd-Hoare automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class EagerReuseCegarLoop<LETTER extends IIcfgTransition<?>> extends BasicCegarLoop<LETTER> {

	
	private final List<AbstractInterpolantAutomaton<LETTER>> mInputFloydHoareAutomata;
	
	private enum MinimizeInitially { NEVER, AFTER_EACH_DIFFERENCE, ONCE_AT_END };
	private final MinimizeInitially mMinimize = MinimizeInitially.AFTER_EACH_DIFFERENCE;

	public EagerReuseCegarLoop(final String name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs, final Collection<? extends IcfgLocation> errorLocs,
			final InterpolationTechnique interpolation, final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final List<AbstractInterpolantAutomaton<LETTER>> inputFloydHoareAutomata) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation, services,
				storage);
		mInputFloydHoareAutomata = inputFloydHoareAutomata;
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();
		
		mLogger.info("Reusing " + mInputFloydHoareAutomata.size() + " Floyd-Hoare automata.");
		for (int i=0; i<mInputFloydHoareAutomata.size(); i++) {
			final AbstractInterpolantAutomaton<LETTER> ai = mInputFloydHoareAutomata.get(i);
			final int internalTransitionsBeforeDifference = ai.computeNumberOfInternalTransitions();
			ai.switchToOnDemandConstructionMode();
			final PowersetDeterminizer<LETTER, IPredicate> psd =
					new PowersetDeterminizer<>(ai, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> diff;
			final boolean explointSigmaStarConcatOfIA = true;
			diff = new Difference<LETTER, IPredicate>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, ai, psd,
					explointSigmaStarConcatOfIA);
			ai.switchToReadonlyMode();
			final int internalTransitionsAfterDifference = ai.computeNumberOfInternalTransitions();
			mLogger.info("Floyd-Hoare automaton" + i + " had " + internalTransitionsAfterDifference + 
					" internal transitions before reuse, on-demand computation of difference added " + 
					(internalTransitionsAfterDifference - internalTransitionsBeforeDifference) + " more.");
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
			
			if (mAbstraction.size() == 0) {
				// stop to compute differences if abstraction is already empty
				break;
			}
			
			if (mMinimize == MinimizeInitially.AFTER_EACH_DIFFERENCE) {
				minimizeAbstractionIfEnabled();
			}
		}
		if (mMinimize == MinimizeInitially.ONCE_AT_END) {
			minimizeAbstractionIfEnabled();
		}
	}
	
	
	
	

}
