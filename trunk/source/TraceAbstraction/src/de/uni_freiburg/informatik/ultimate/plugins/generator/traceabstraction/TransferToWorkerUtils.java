package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class TransferToWorkerUtils<LETTER, STATE> {

	private final ILogger mLogger;
	private final ManagedScript mMainScript;
	private final ManagedScript mWorkerScript;
	private final HashMap<LETTER, LETTER> mEdgeCache = new HashMap<>();
	private final AutomataLibraryServices mServices;
	TermTransferrer mWorker2main;
	TermTransferrer mMain2worker;
	VpAlphabet<LETTER> mMainVpAlphabet;
	VpAlphabet<LETTER> mWorkerVpAlphabet;

	enum Mode {
		NONE, MAIN2WORKER, WORKER2MAIN
	}

	private Mode mMode = Mode.NONE;

	/**
	 * Utils class for transferring formulas, terms and things that contain terms to
	 * the worker script
	 *
	 * @param main
	 * @param worker
	 */
	public TransferToWorkerUtils(final AutomataLibraryServices services, final ILogger logger, final ManagedScript main,
			final ManagedScript worker) {
		mLogger = logger;
		mMainScript = main;
		mWorkerScript = worker;
		mServices = services;

		mWorker2main = new TermTransferrer(worker.getScript(), main.getScript());
		mMain2worker = new TermTransferrer(main.getScript(), worker.getScript());
	}

	public void setMode(final Mode mode) {
		mMode = mode;
	}

	// TODO put this and anything for worker setup in an extrac class then alter
	// call it in the worker not in main
	public NestedRun<LETTER, ?> transferRun(final NestedRun<LETTER, ?> counterexample) {
		final NestedRun<LETTER, ?> oldCounterexample = counterexample;

		NestedWord<LETTER> currentWord = new NestedWord<>();
		for (int i = 0; i < oldCounterexample.getWord().length(); i++) {
			final LETTER letter = oldCounterexample.getWord().asList().get(i);
			int nestingOperation = NestedWord.INTERNAL_POSITION;
			switch (letter) {
			case final Call call -> nestingOperation = NestedWord.PLUS_INFINITY;
			case final Return re -> nestingOperation = NestedWord.MINUS_INFINITY;
			case final StatementSequence stmt -> nestingOperation = NestedWord.INTERNAL_POSITION;
			default -> new AssertionError("Unexpected letter type: " + letter.getClass());
			}
			final NestedWord<LETTER> singleWord = new NestedWord<>(transferEdge(letter), nestingOperation);
			currentWord = currentWord.concatenate(singleWord);

		}

		final NestedRun<LETTER, ?> workerCounterexample = new NestedRun<>(currentWord,
				oldCounterexample.getStateSequence());
		return workerCounterexample;
	}

	private LETTER transferEdge(final LETTER letter) {
		LETTER transferredLetter = null;
		if (mEdgeCache.containsKey(letter)) {
			transferredLetter = mEdgeCache.get(letter);
		} else {
			switch (letter) {
			case final Call call -> transferredLetter = (LETTER) getTransferCall(call);
			case final Return re -> transferredLetter = (LETTER) getTransferReturn(re);
			case final StatementSequence stmt -> transferredLetter = (LETTER) getTransferStmtSequence(stmt);
			default -> new AssertionError("Unexpected letter type: " + letter.getClass());
			}
		}
		assert transferredLetter != null;
		mEdgeCache.put(letter, transferredLetter);
		mEdgeCache.put(transferredLetter, letter);
		return transferredLetter;
	}

	private Call getTransferCall(final Call call) {
		final Call newCall = new Call(call.getSerialNumber(), (BoogieIcfgLocation) call.getSource(),
				(BoogieIcfgLocation) call.getTarget(), call.getCallStatement(), mLogger);
		newCall.setTransitionFormula(transferTransFormulaWithMode(call.getTransformula()));
		return newCall;
	}

	private StatementSequence getTransferStmtSequence(final StatementSequence stmt) {
		final StatementSequence newStmt = new StatementSequence(stmt.getSerialNumber(),
				(BoogieIcfgLocation) stmt.getSource(), (BoogieIcfgLocation) stmt.getTarget(), stmt.getStatements(),
				mLogger);
		newStmt.setTransitionFormula(transferTransFormulaWithMode(stmt.getTransformula()));
		return newStmt;

	}

	private Return getTransferReturn(final Return re) {
		final Return newReturn = new Return(re.getSerialNumber(), (BoogieIcfgLocation) re.getSource(),
				(BoogieIcfgLocation) re.getTarget(), re.getCorrespondingCall(), mLogger);
		newReturn.setTransitionFormula(transferTransFormulaWithMode(re.getTransformula()));
		return newReturn;

	}

	private UnmodifiableTransFormula transferTransFormulaWithMode(final UnmodifiableTransFormula inTF) {
		switch (mMode) {
		case MAIN2WORKER: {
			return transferTransformula(inTF, mMain2worker, mWorkerScript);
		}
		case WORKER2MAIN: {
			return transferTransformula(inTF, mWorker2main, mMainScript);
		}
		default: {
			throw new AssertionError("Unexpected transferrer mode: " + mMode);
		}
		}
	}

	private UnmodifiableTransFormula transferTransformula(final UnmodifiableTransFormula inTF,
			final TermTransferrer transferrer, final ManagedScript targetScript) {
		final TransFormulaBuilder transferredTF = new TransFormulaBuilder(transferMap(transferrer, inTF.getInVars()),
				transferMap(transferrer, inTF.getOutVars()), inTF.getNonTheoryConsts().isEmpty(),
				inTF.getNonTheoryConsts(), inTF.getBranchEncoders().isEmpty(),
				transferSet(transferrer, inTF.getBranchEncoders()), inTF.getAuxVars().isEmpty());

		transferredTF.setFormula(transferrer.transform(inTF.getFormula()));

		transferredTF.addAuxVarsButRenameToFreshCopies(transferSet(transferrer, inTF.getAuxVars()), targetScript);

		transferredTF.setInfeasibility(inTF.isInfeasible());
		return transferredTF.finishConstruction(targetScript);

	}

	private static Map<IProgramVar, TermVariable> transferMap(final TermTransferrer transferrer,
			final Map<IProgramVar, TermVariable> map) {
		final Map<IProgramVar, TermVariable> transferredMap = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : map.entrySet()) {
			transferredMap.put(entry.getKey(), (TermVariable) transferrer.transform(entry.getValue()));
		}
		return transferredMap;
	}

	public static Set<TermVariable> transferSet(final TermTransferrer transferrer, final Set<TermVariable> inputSet) {
		final Set<TermVariable> outSet = new HashSet<>();
		for (final TermVariable var : inputSet) {
			outSet.add((TermVariable) transferrer.transform(var));
		}
		return outSet;
	}

	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> transferAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton,
			final IEmptyStackStateFactory<STATE> emptyStateFactory) {

		VpAlphabet<LETTER> alphabet;
		Set<LETTER> internalAlphabet;
		Set<LETTER> callAlphabet;
		Set<LETTER> returnAlphabet;

		switch (mMode) {
		case MAIN2WORKER: {
			internalAlphabet = new HashSet<>();
			callAlphabet = new HashSet<>();
			returnAlphabet = new HashSet<>();
			mMainVpAlphabet = automaton.getVpAlphabet();
			alphabet = new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet);
			break;
		}
		case WORKER2MAIN: {
			internalAlphabet = mMainVpAlphabet.getInternalAlphabet();
			callAlphabet = mMainVpAlphabet.getCallAlphabet();
			returnAlphabet = mMainVpAlphabet.getReturnAlphabet();
			alphabet = mMainVpAlphabet;
			break;
		}
		default: {
			throw new AssertionError("Unexpected transferrer mode: " + mMode);
		}
		}

		final NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(mServices, alphabet,
				emptyStateFactory);

		
		final Set<STATE> hierPredStates = new HashSet<STATE>();
		hierPredStates.add(automaton.getEmptyStackState());
		final Set<STATE> allStates = new HashSet<STATE>();
		
		final Set<STATE> initialStates = new HashSet<STATE>();
		automaton.getInitialStates().forEach(initialStates::add);
		final ArrayDeque<STATE> dequeue = new ArrayDeque<>(initialStates);
		
	
		

		final Set<STATE> visited = new HashSet<>();
		while (!dequeue.isEmpty()) {
			final STATE state = dequeue.pop();

			if (!visited.add(state)) {
				continue;
			}
			if (!result.contains(state)) {
				allStates.add(state);
				result.addState(automaton.isInitial(state), automaton.isFinal(state), state);
			}

			for (final OutgoingCallTransition<LETTER, STATE> transition : automaton.callSuccessors(state)) {
				final STATE succesor = transition.getSucc();
				if (!result.contains(succesor)) {
					result.addState(automaton.isInitial(succesor), automaton.isFinal(succesor), succesor);
				}
				final LETTER transferredLetter = transferEdge(transition.getLetter());
				callAlphabet.add(transferredLetter);
				result.addCallTransition(state, transferredLetter, succesor);
				hierPredStates.add(state);
				dequeue.add(succesor);
			}
			for (final OutgoingInternalTransition<LETTER, STATE> transition : automaton.internalSuccessors(state)) {
				final STATE succesor = transition.getSucc();
				if (!result.contains(succesor)) {
					result.addState(automaton.isInitial(succesor), automaton.isFinal(succesor), succesor);
				}
				final LETTER transferredLetter = transferEdge(transition.getLetter());
				internalAlphabet.add(transferredLetter);
				result.addInternalTransition(state, transferredLetter, succesor);
				dequeue.add(succesor);
			}

		}

		for (final STATE state : allStates) {
			for (final STATE hierPred : hierPredStates) {
				for (final OutgoingReturnTransition<LETTER, STATE> returnTransition : automaton
						.returnSuccessorsGivenHier(state, hierPred)) {

					STATE succesor = returnTransition.getSucc();
					STATE hier = returnTransition.getHierPred();
					if (!result.contains(succesor)) {
						result.addState(automaton.isInitial(succesor), automaton.isFinal(succesor), succesor);
					}
					if (!result.contains(hier)) {
						result.addState(automaton.isInitial(hier), automaton.isFinal(hier), hier);
					}
					final LETTER transferredLetter = transferEdge(returnTransition.getLetter());
					returnAlphabet.add(transferredLetter);
					result.addReturnTransition(state, hier, transferredLetter, succesor);
				}
			}
		}

		
		return result;

	}

}
