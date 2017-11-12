package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementNCSBLazyNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementNCSBNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

public class ComplementTest<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final AutomataLibraryServices mServices;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndComplemented;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndComplementedStandard;
	
	public <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>>  
	ComplementTest(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataLibraryException {
		mOperand = operand;
		mServices = services;
	    testComplement(stateFactory);
	}
	static int mNumber = 0;
	private <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
	void testComplement(final SF stateFactory) throws AutomataLibraryException {
		 IBuchiComplementNcsbStateFactory<STATE> ncsbSf = (IBuchiComplementNcsbStateFactory<STATE>)stateFactory;
		final BuchiComplementNCSBLazyNwa<LETTER, STATE> onDemandComplemented = new BuchiComplementNCSBLazyNwa<>(mServices, ncsbSf, mOperand);
		Options.lazyB = false;
		Options.lazyS = true;
		mSndComplemented = new NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE>(onDemandComplemented);
		final BuchiComplementNCSBNwa<LETTER, STATE> complemented = new BuchiComplementNCSBNwa<>(mServices, ncsbSf, mOperand, false);
		mSndComplementedStandard = new NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE>(complemented);
		mNumber ++;
		new AutomatonDefinitionPrinter<String, String>(mServices, "complement",
		"./complement" + mNumber + "_1", Format.BA, "", mSndComplemented);
		new AutomatonDefinitionPrinter<String, String>(mServices, "complement",
		"./complement" + mNumber + "_2", Format.BA, "", mSndComplementedStandard);
	}

}
