/*
 * Copyright (C) 2025 University of Freiburg
 * Copyright (C) 2025 LMU Munich
 * Copyright (C) 2025 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
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
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.LocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class TransferBetweenMainAndWorker<LETTER, STATE> {

	private final ILogger mLogger;
	private final ManagedScript mMainScript;
	private final ManagedScript mWorkerScript;
	private final HashMap<LETTER, LETTER> mEdgeCache = new HashMap<>(); // Bidirectional
	private final HashMap<IProgramVar, IProgramVar> mProgramVarBackTranslationCache = new HashMap<>(); // Maps worker ->
																										// main
	private final AutomataLibraryServices mServices;
	private final TermTransferrer mWorker2main;
	private final TermTransferrer mMain2worker;
	private VpAlphabet<LETTER> mMainVpAlphabet;
	private final CfgSmtToolkit mMainCsToolkit;
	private final ProgramVariableTransferrer mVarTransfer;

	enum Mode {
		NONE, MAIN2WORKER, WORKER2MAIN
	}

	private Mode mMode = Mode.NONE;

	/**
	 * A class used to transfer runs / cex and automata between worker and main scripts. Also used to create the worker
	 * CfgToolKit. Every creation of worker IProgramVars should run through this classes @VariableTransferrer
	 *
	 * On initialization this classes creates the workers ManagedScript. And the necessary TermTransferrer
	 *
	 * @param main
	 * @param worker
	 * @param mainCfgToolKit
	 *
	 * @author Max Barth (max.barth@lmu.de)
	 */
	public TransferBetweenMainAndWorker(final AutomataLibraryServices services, final ILogger logger,
			final ManagedScript main, final IUltimateServiceProvider solverServices,
			final SolverSettings solverSettings, final CfgSmtToolkit mainCfgToolKit) {
		mLogger = logger;
		mMainScript = main;
		mWorkerScript = mainCfgToolKit.createFreshManagedScript(solverServices, solverSettings);

		mServices = services;
		mMainCsToolkit = mainCfgToolKit;

		mWorker2main = new TermTransferrer(mWorkerScript.getScript(), mMainScript.getScript());
		mMain2worker = new TermTransferrer(mMainScript.getScript(), mWorkerScript.getScript());
		mVarTransfer = new ProgramVariableTransferrer(mMain2worker, mWorkerScript);

		mWorkerScript.copyVariableManager(mWorkerScript.getVariableManager().getTvForBasenameCounter(),
				transferTv2StringMap(mMain2worker, mWorkerScript.getVariableManager().getTv2Basename()),
				mWorkerScript.getVariableManager().getVariableNames());
	}

	/*
	 * Gets a run / counterexample with Letters whose transformula comes from one script. Returns a new run with new
	 * letters, whose transformula comes from target script. The semantics of both runs are equal.
	 */
	public IRun<LETTER, ?> transferRun(final NestedRun<LETTER, ?> counterexample, final Mode mode) {
		final NestedRun<LETTER, ?> oldCounterexample = counterexample;
		mMode = mode;
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

		final NestedRun<LETTER, ?> workerCounterexample =
				new NestedRun<>(currentWord, oldCounterexample.getStateSequence());
		return workerCounterexample;
	}

	// Caches every transferred Edge bidirectional
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
		newCall.setPayload(call.getPayload()); // Payload is need for for example Overaprixmation Annotations
		return newCall;
	}

	private StatementSequence getTransferStmtSequence(final StatementSequence stmt) {
		final StatementSequence newStmt =
				new StatementSequence(stmt.getSerialNumber(), (BoogieIcfgLocation) stmt.getSource(),
						(BoogieIcfgLocation) stmt.getTarget(), stmt.getStatements(), mLogger);
		newStmt.setTransitionFormula(transferTransFormulaWithMode(stmt.getTransformula()));
		newStmt.setPayload(stmt.getPayload());
		return newStmt;

	}

	private Return getTransferReturn(final Return re) {
		final Return newReturn = new Return(re.getSerialNumber(), (BoogieIcfgLocation) re.getSource(),
				(BoogieIcfgLocation) re.getTarget(), getTransferCall(re.getCorrespondingCall()), mLogger);
		newReturn.setTransitionFormula(transferTransFormulaWithMode(re.getTransformula()));
		newReturn.setPayload(re.getPayload());
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
		assert inTF.getNonTheoryConsts().isEmpty();
		transferredTF.setFormula(transferrer.transform(inTF.getFormula()));

		transferredTF.addAuxVarsButRenameToFreshCopies(transferSet(transferrer, inTF.getAuxVars()), targetScript);

		transferredTF.setInfeasibility(inTF.isInfeasible());
		return transferredTF.finishConstruction(targetScript);

	}

	private Map<TermVariable, String> transferTv2StringMap(final TermTransferrer transferrer,
			final Map<TermVariable, String> map) {
		final Map<TermVariable, String> transferredMap = new HashMap<>();
		for (final Entry<TermVariable, String> entry : map.entrySet()) {
			transferredMap.put((TermVariable) transferrer.transform(entry.getKey()), entry.getValue());
		}
		return transferredMap;
	}

	private Map<IProgramVar, TermVariable> transferMap(final TermTransferrer transferrer,
			final Map<IProgramVar, TermVariable> map) {
		final Map<IProgramVar, TermVariable> transferredMap = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : map.entrySet()) {
			IProgramVar transferredProgramVar;
			if (!mProgramVarBackTranslationCache.containsKey(entry.getKey())) {
				assert mMode.equals(Mode.MAIN2WORKER);
				switch (entry.getKey()) {
				case final ProgramNonOldVar var -> {
					transferredProgramVar = mVarTransfer.translateProgramVar(var);
					break;
				}
				case final LocalProgramVar var -> {
					transferredProgramVar = mVarTransfer.translateProgramVar(var);
					break;
				}
				default -> throw new AssertionError("Unexpected type of BoogieVar: " + entry.getKey().getClass());
				}
				mProgramVarBackTranslationCache.put(transferredProgramVar, entry.getKey());
			} else {
				transferredProgramVar = mProgramVarBackTranslationCache.get(entry.getKey());
			}
			assert transferredProgramVar != null;
			transferredMap.put(transferredProgramVar, (TermVariable) transferrer.transform(entry.getValue()));
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

	/**
	 * This method gets an @INwaOutgoingLetterAndTransitionProvider and returns
	 * an @INwaOutgoingLetterAndTransitionProvider
	 *
	 * Thereby, it explores the input automaton and creates the output automaton. States remain the same, Letters are
	 * transferred from one script to another depending on the @mode. The new automaton has a new Alphabet, and can have
	 * less transitions than the input automaton. TODO check if this can really be sound
	 */
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> transferAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton,
			final IEmptyStackStateFactory<STATE> emptyStateFactory, final Mode mode) {

		VpAlphabet<LETTER> alphabet;
		Set<LETTER> internalAlphabet;
		Set<LETTER> callAlphabet;
		Set<LETTER> returnAlphabet;
		mMode = mode;
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
			alphabet = new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet);
			break;
		}
		default: {
			throw new AssertionError("Unexpected transferrer mode: " + mMode);
		}
		}

		final NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<>(mServices, alphabet, emptyStateFactory);

		final Set<STATE> hierPredStates = new HashSet<>();
		hierPredStates.add(automaton.getEmptyStackState());
		final Set<STATE> allStates = new HashSet<>();

		final Set<STATE> initialStates = new HashSet<>();
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
					allStates.add(succesor);
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
					allStates.add(succesor);
					result.addState(automaton.isInitial(succesor), automaton.isFinal(succesor), succesor);
				}
				final LETTER transferredLetter = transferEdge(transition.getLetter());
				internalAlphabet.add(transferredLetter);
				result.addInternalTransition(state, transferredLetter, succesor);
				dequeue.add(succesor);
			}
			final Set<STATE> copyAllStates = new HashSet<>(allStates);
			for (final STATE potentialhier : copyAllStates) {
				for (final STATE hierPred : hierPredStates) {
					for (final OutgoingReturnTransition<LETTER, STATE> returnTransition : automaton
							.returnSuccessorsGivenHier(potentialhier, hierPred)) {

						final STATE succesor = returnTransition.getSucc();
						final STATE hier = returnTransition.getHierPred();
						if (!result.contains(succesor)) {
							allStates.add(succesor);
							result.addState(automaton.isInitial(succesor), automaton.isFinal(succesor), succesor);
						}
						if (!result.contains(hier)) {
							allStates.add(hier);
							result.addState(automaton.isInitial(hier), automaton.isFinal(hier), hier);
						}
						final LETTER transferredLetter = transferEdge(returnTransition.getLetter());
						returnAlphabet.add(transferredLetter);
						result.addReturnTransition(potentialhier, hier, transferredLetter, succesor);
						dequeue.add(succesor);
					}
				}
			}
			// TODO transfer summaries, so far they are ignored because i dont know how to detect a summary in the input
		}
		assert result.size() == automaton.size();
		return result;

	}

	public CfgSmtToolkit constructWorkerCfgSmtToolkit() {
		final HashRelation<String, IProgramNonOldVar> proc2globals =
				constructNewProc2Globals(mMainCsToolkit.getModifiableGlobalsTable().getProcToGlobals(), mVarTransfer);
		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);
		final IIcfgSymbolTable symbolTable =
				constructNewSymbolTable(mMainCsToolkit.getSymbolTable(), mMainCsToolkit.getProcedures(), mVarTransfer);
		final Map<String, List<ILocalProgramVar>> inParams =
				constructNewParams(mMainCsToolkit.getInParams(), mVarTransfer);
		final Map<String, List<ILocalProgramVar>> outParams =
				constructNewParams(mMainCsToolkit.getOutParams(), mVarTransfer);

		final IPredicate mainAxioms = mMainCsToolkit.getSmtFunctionsAndAxioms().getAxioms();
		final Set<IProgramVar> vars = new HashSet<>();
		for (final IProgramVar var : mainAxioms.getVars()) {
			vars.add(mVarTransfer.translateProgramVar(var));
		}
		final Set<IProgramFunction> funs = new HashSet<>();
		for (final IProgramFunction fun : mainAxioms.getFuns()) {
			// TODO what is a IProgramFunction? Does this do the trick?
			funs.add(mVarTransfer.getOrConstruct((IProgramConst) fun));
		}
		final IPredicate newAxiomsPred = new BasicPredicate(0, mMain2worker.transform(mainAxioms.getFormula()), vars,
				funs, mMain2worker.transform(mainAxioms.getClosedFormula()));
		final SmtFunctionsAndAxioms smtFunctionsAndAxioms = new SmtFunctionsAndAxioms(newAxiomsPred, mWorkerScript);
		return new CfgSmtToolkit(modifiableGlobalsTable, mWorkerScript, symbolTable, mMainCsToolkit.getProcedures(),
				inParams, outParams, mMainCsToolkit.getIcfgEdgeFactory(), mMainCsToolkit.getConcurrencyInformation(),
				smtFunctionsAndAxioms);
	}

	private static Map<String, List<ILocalProgramVar>> constructNewParams(
			final Map<String, List<ILocalProgramVar>> inParams, final ProgramVariableTransferrer variableTranslation) {
		final Map<String, List<ILocalProgramVar>> result = new HashMap<>();
		for (final Entry<String, List<ILocalProgramVar>> entry : inParams.entrySet()) {
			final List<ILocalProgramVar> newList = entry.getValue().stream()
					.map(x -> variableTranslation.getOrConstruct(x)).collect(Collectors.toList());
			result.put(entry.getKey(), newList);
		}
		return result;
	}

	private static IIcfgSymbolTable constructNewSymbolTable(final IIcfgSymbolTable symbolTable,
			final Set<String> procedures, final ProgramVariableTransferrer varTrans) {
		final DefaultIcfgSymbolTable result = new DefaultIcfgSymbolTable();
		for (final IProgramConst c : symbolTable.getConstants()) {
			result.add(varTrans.getOrConstruct(c));
		}
		for (final IProgramNonOldVar g : symbolTable.getGlobals()) {
			result.add(varTrans.getOrConstruct(g));
		}
		for (final String proc : procedures) {
			for (final ILocalProgramVar l : symbolTable.getLocals(proc)) {
				result.add(varTrans.getOrConstruct(l));
			}
		}
		return result;
	}

	private static HashRelation<String, IProgramNonOldVar> constructNewProc2Globals(
			final HashRelation<String, IProgramNonOldVar> procToGlobals,
			final ProgramVariableTransferrer variableTranslation) {
		final HashRelation<String, IProgramNonOldVar> result = new HashRelation<>();
		for (final Entry<String, HashSet<IProgramNonOldVar>> entry : procToGlobals.entrySet()) {
			for (final IProgramNonOldVar old : entry.getValue()) {
				final IProgramNonOldVar newVar = variableTranslation.getOrConstruct(old);
				result.addPair(entry.getKey(), newVar);
			}
		}
		return result;
	}

}