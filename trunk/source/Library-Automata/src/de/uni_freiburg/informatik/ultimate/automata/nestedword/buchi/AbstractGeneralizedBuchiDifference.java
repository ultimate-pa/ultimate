package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.AbstractGeneralizedAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.BuchiDifferenceTest;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.ComplementNwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.ComplementTest;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.GeneralizedNestedWordAutomatonReachableStatesAntichain;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public abstract class AbstractGeneralizedBuchiDifference<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {


	protected final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	protected final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	protected ComplementNwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> mSndComplemented;
	protected AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> mResult;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public <SF extends IBuchiComplementNcsbStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> AbstractGeneralizedBuchiDifference(
			final AutomataLibraryServices services, final SF stateFactory,
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand, boolean lazyOptimization) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		
		if (!NestedWordAutomataUtils.isFiniteAutomaton(sndOperand)) {
			throw new UnsupportedOperationException("Calls and returns are not yet supported.");
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		constructResult(stateFactory, lazyOptimization);
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}

//		new ComplementTest<>(mServices, stateFactory, mSndOperand);
//		new BuchiDifferenceTest<>(mServices, stateFactory, getResult(), mFstOperand, mSndOperand);
	}

	protected <SF extends IBuchiComplementNcsbStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
			void constructResult(final SF stateFactory, final boolean lazyOptimization) throws AutomataLibraryException {
		// first we get the complement
		final BuchiComplementNCSBSimpleNwa<LETTER, STATE> onDemandComplemented = new BuchiComplementNCSBSimpleNwa<>(mServices, stateFactory, mSndOperand);
		Options.lazyS = lazyOptimization;
		Options.lazyB = false;
		mSndComplemented = new ComplementNwaOutgoingLetterAndTransitionAdapter<LETTER, STATE>(onDemandComplemented);
		constructDifferenceFromComplement(stateFactory);
	}

	protected abstract <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> void constructDifferenceFromComplement(SF stateFactory)
			throws AutomataLibraryException;

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". First operand " + mFstOperand.sizeInformation() + ". Second operand "
				+ mSndOperand.sizeInformation() + " Result " + mResult.sizeInformation() + " Complement of second has "
				+ getSndComplemented().size() + " states.";
	}
		
	@Override
	public final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}

	@Override
	public final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}
	
	public final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSndComplemented() {
		return mSndComplemented;
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		final boolean underApproximationOfComplement = false;
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}

		final List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<>();
		final GeneralizedBuchiIsEmpty<LETTER, STATE> fstOperandEmptiness = new GeneralizedBuchiIsEmpty<>(mServices, mFstOperand);
		final boolean fstOperandEmpty = fstOperandEmptiness.getResult();
		if (!fstOperandEmpty) {
			lassoWords.add(fstOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> sndOperandEmptiness = new BuchiIsEmpty<>(mServices, mSndOperand);
		final boolean sndOperandEmpty = sndOperandEmptiness.getResult();
		if (!sndOperandEmpty) {
			lassoWords.add(sndOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final GeneralizedBuchiIsEmpty<LETTER, STATE> resultEmptiness = new GeneralizedBuchiIsEmpty<>(mServices, mResult);
		final boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		boolean correct = true;
		correct &= (!fstOperandEmpty || resultEmpty);
		assert correct;
//		lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, mResult.size(), 0));
//		lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, mFstOperand.size(), 1));
//		lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, mSndOperand.size(), 2));
//		lassoWords.addAll((new LassoExtractor<>(mServices, mFstOperand)).getResult());
//		lassoWords.addAll((new LassoExtractor<>(mServices, mSndOperand)).getResult());
//		lassoWords.addAll((new LassoExtractor<>(mServices, mResult)).getResult());
//
//		for (final NestedLassoWord<LETTER> nlw : lassoWords) {
//			correct &= checkAcceptance(nlw, mFstOperand, mSndOperand, underApproximationOfComplement);
//			assert correct;
//		}
//		if (!correct) {
//			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
//					"language is different", mFstOperand, mSndOperand);
//		}
//		if (mLogger.isInfoEnabled()) {
//			mLogger.info("Finished testing correctness of " + getOperationName());
//		}
		return correct;
	}

	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand1,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand2, final boolean underApproximationOfComplement)
			throws AutomataLibraryException {
		boolean correct;
		final boolean op1 = (new BuchiAccepts<>(mServices, operand1, nlw)).getResult();
		final boolean op2 = (new BuchiAccepts<>(mServices, operand2, nlw)).getResult();
		final boolean res = (new BuchiAccepts<>(mServices, mResult, nlw)).getResult();
		if (res) {
			correct = op1 && !op2;
		} else {
			correct = !(!underApproximationOfComplement && op1 && !op2);
		}
		assert correct : getOperationName() + " wrong result!";
		return correct;
	}

}

