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
