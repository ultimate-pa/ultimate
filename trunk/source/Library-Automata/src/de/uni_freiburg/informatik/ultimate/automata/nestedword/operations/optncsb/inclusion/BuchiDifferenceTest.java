package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementNCSBLazyNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementNCSBNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

public class BuchiDifferenceTest<LETTER, STATE> {
	
	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INestedWordAutomaton<LETTER, STATE> mDifference;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private final AutomataLibraryServices mServices;
	private final IBuchiIntersectStateFactory<STATE> mStateFactory;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndComplemented;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndComplementedStandard;
	
	public <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>>  
	 BuchiDifferenceTest(
			final AutomataLibraryServices services, final SF stateFactory,
			final INestedWordAutomaton<LETTER, STATE> difference,
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mServices = services;
		mDifference = difference;
	    mStateFactory = stateFactory;
	    constructDifference(stateFactory);
	}
	
    static int mNumber = 0;
	private <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
	void constructDifference(final SF stateFactory) throws AutomataLibraryException {
		INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOp = new GeneralizedBuchiToBuchi<>(stateFactory, mFstOperand);
		IBuchiComplementNcsbStateFactory<STATE> sf = (IBuchiComplementNcsbStateFactory<STATE>)stateFactory;
		final BuchiComplementNCSBNwa<LETTER, STATE> onDemandComplemented = new BuchiComplementNCSBNwa<>(mServices,
				sf, mSndOperand, false);
		mSndComplemented = new NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE>(onDemandComplemented);
		BuchiIntersectNwa<LETTER, STATE> diff = new BuchiIntersectNwa<>(fstOp, mSndComplemented, stateFactory);
		NestedWordAutomatonReachableStates<LETTER, STATE> reach = new NestedWordAutomatonReachableStates<>(mServices, diff);
		INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> baDiff = new GeneralizedBuchiToBuchi<>(stateFactory, mDifference);
		NestedWordAutomatonReachableStates<LETTER, STATE> reachBADiff = new NestedWordAutomatonReachableStates<>(mServices, baDiff);
		mNumber ++;
		new AutomatonDefinitionPrinter<String, String>(mServices, "difference",
		"./difference" + mNumber + "_1", Format.BA, "", reachBADiff);
		new AutomatonDefinitionPrinter<String, String>(mServices, "difference",
		"./difference" + mNumber + "_2", Format.BA, "", reach);
		BuchiIsEmpty<LETTER, STATE> check = new BuchiIsEmpty<>(mServices, reach);
		System.err.println("Difference empty from BA: " + check.getResult());
		check = new BuchiIsEmpty<>(mServices, reachBADiff);
		System.err.println("Difference empty from GBA: " + check.getResult());
		BenchmarkRecord.addDiffComparison(reach.getStates().size(), mDifference.getStates().size(), reachBADiff.getStates().size());
	}
	

}
