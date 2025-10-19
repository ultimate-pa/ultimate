package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.LocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class TransferBetweenMainAndWorker<LETTER, STATE> {

	private final ILogger mLogger;
	private final ManagedScript mMainScript;
	private final ManagedScript mWorkerScript;
	private final HashMap<LETTER, LETTER> mEdgeCache = new HashMap<>(); //Bidirectional
	private final HashMap<IProgramVar, IProgramVar> mProgramVarBackTranslationCache = new HashMap<>(); //Maps worker -> main
	private final AutomataLibraryServices mServices;
	private final TermTransferrer mWorker2main;
	private final TermTransferrer mMain2worker;
	private VpAlphabet<LETTER> mMainVpAlphabet;
	private final CfgSmtToolkit mMainCsToolkit;
private VariableTransferrer mVarTransfer;
	
	enum Mode {
		NONE, MAIN2WORKER, WORKER2MAIN
	}

	private Mode mMode = Mode.NONE;

	/**
	 * A class used to transfer runs and automata between worker and main scripts.
	 * Also used to create the worker CfgToolKit.
	 * Every creation of worker IProgramVars should run through this classes @VariableTransferrer
	 *
	 * On initialization this classes creates the workers ManagedScript 
	 *
	 * @param main
	 * @param worker
	 * @param mainCfgToolKit
	 */
	public TransferBetweenMainAndWorker(final AutomataLibraryServices services, final ILogger logger, final ManagedScript main,
			final IUltimateServiceProvider solverServices,
			final SolverSettings solverSettings , CfgSmtToolkit mainCfgToolKit) {
		mLogger = logger;
		mMainScript = main;
		mWorkerScript = mainCfgToolKit.createFreshManagedScript(solverServices, solverSettings);
		mServices = services;
		mMainCsToolkit = mainCfgToolKit;
		
		mWorker2main = new TermTransferrer(mWorkerScript.getScript(), mMainScript.getScript());
		mMain2worker = new TermTransferrer(mMainScript.getScript(), mWorkerScript.getScript());
		mVarTransfer = new VariableTransferrer(mMain2worker,mWorkerScript);
	}

	/*
	 * Gets a run / counterexample with Letters whose transformula comes from one script.
	 * Returns a new run with new letters, whose transformula comes from target script.
	 * The semantics of both runs are equal
	 */
	public IRun<LETTER, ?> transferRun(final NestedRun<LETTER, ?> counterexample, Mode mode) {
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
		newCall.setPayload(call.getPayload());
		return newCall;
	}

	private StatementSequence getTransferStmtSequence(final StatementSequence stmt) {
		final StatementSequence newStmt = new StatementSequence(stmt.getSerialNumber(),
				(BoogieIcfgLocation) stmt.getSource(), (BoogieIcfgLocation) stmt.getTarget(), stmt.getStatements(),
				mLogger);
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

	private Map<IProgramVar, TermVariable> transferMap(final TermTransferrer transferrer,
			final Map<IProgramVar, TermVariable> map) {
		final Map<IProgramVar, TermVariable> transferredMap = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : map.entrySet()) {
			IProgramVar transferredProgramVar;
			if (!mProgramVarBackTranslationCache.containsKey(entry.getKey())) {
				assert mMode.equals(Mode.MAIN2WORKER);
				switch (entry.getKey()) {				
				case ProgramNonOldVar var -> {
					transferredProgramVar = mVarTransfer.translateProgramVar(var);
					break;
				}
				case LocalProgramVar var -> {
					transferredProgramVar = mVarTransfer.translateProgramVar(var);
					break;
				}
				default -> throw new AssertionError("Unexpected type of BoogieVar: " + entry.getKey().getClass());
				}
				mProgramVarBackTranslationCache.put(transferredProgramVar,entry.getKey());
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
	 * This method gets an @INwaOutgoingLetterAndTransitionProvider and returns an @INwaOutgoingLetterAndTransitionProvider
	 * 
	 * Thereby, it explores the input automaton and creates the output automaton.
	 * States remain the same, Letters are transferred from one script to another depending on the @mode.
	 * The new automaton has a new Alphabet, and can have less transitions than the input automaton.
	 * TODO check if this can really be sound
	 */
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> transferAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton,
			final IEmptyStackStateFactory<STATE> emptyStateFactory, Mode mode) {

		VpAlphabet<LETTER> alphabet;
		Set<LETTER> internalAlphabet;
		Set<LETTER> callAlphabet;
		Set<LETTER> returnAlphabet;
		mMode  = mode;
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
			Set<STATE> copyAllStates = new HashSet<>();
			copyAllStates.addAll(allStates);
			for (final STATE potentialhier : copyAllStates) {
				for (final STATE hierPred : hierPredStates) {
					for (final OutgoingReturnTransition<LETTER, STATE> returnTransition : automaton
							.returnSuccessorsGivenHier(potentialhier, hierPred)) {

						STATE succesor = returnTransition.getSucc();
						STATE hier = returnTransition.getHierPred();
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
		}
		// TODO summaries missing, internal alphabet thus smaller
		assert result.size() == automaton.size();
		return result;

	}

	public CfgSmtToolkit constructWorkerCfgSmtToolkit() {

		final HashRelation<String, IProgramNonOldVar> proc2globals = constructNewProc2Globals(
				mMainCsToolkit.getModifiableGlobalsTable().getProcToGlobals(), mVarTransfer);
		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);
		final IIcfgSymbolTable symbolTable = constructNewSymbolTable(mMainCsToolkit.getSymbolTable(),
				mMainCsToolkit.getProcedures(), mVarTransfer);
		final Map<String, List<ILocalProgramVar>> inParams = constructNewParams(mMainCsToolkit.getInParams(), mVarTransfer);
		final Map<String, List<ILocalProgramVar>> outParams = constructNewParams(mMainCsToolkit.getOutParams(), mVarTransfer);
		final SmtFunctionsAndAxioms smtFunctionsAndAxioms = null;
		return new CfgSmtToolkit(modifiableGlobalsTable, mWorkerScript, symbolTable, mMainCsToolkit.getProcedures(),
				inParams, outParams, mMainCsToolkit.getIcfgEdgeFactory(), mMainCsToolkit.getConcurrencyInformation(),
				smtFunctionsAndAxioms);
	}

	private static Map<String, List<ILocalProgramVar>> constructNewParams(
			final Map<String, List<ILocalProgramVar>> inParams, final VariableTransferrer variableTranslation) {
		final Map<String, List<ILocalProgramVar>> result = new HashMap<>();
		for (final Entry<String, List<ILocalProgramVar>> entry : inParams.entrySet()) {
			final List<ILocalProgramVar> newList = entry.getValue().stream()
					.map(x -> variableTranslation.getOrConstruct(x)).collect(Collectors.toList());
			result.put(entry.getKey(), newList);
		}
		return result;
	}

	private static IIcfgSymbolTable constructNewSymbolTable(final IIcfgSymbolTable symbolTable,
			final Set<String> procedures, final VariableTransferrer varTrans) {
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
			final HashRelation<String, IProgramNonOldVar> procToGlobals, final VariableTransferrer variableTranslation) {
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

class VariableTransferrer {
	private final ConstructionCache<ILocalProgramVar, ILocalProgramVar> mILocalProgramVarCC;
	private final ConstructionCache<IProgramNonOldVar, IProgramNonOldVar> mIProgramNonOldVarCC;
	private final ConstructionCache<IProgramConst, IProgramConst> mIProgramConstCC;

	public VariableTransferrer(TermTransferrer transferrer, ManagedScript targetScript	) {
		mILocalProgramVarCC = new ConstructionCache<>(new IValueConstruction<ILocalProgramVar, ILocalProgramVar>() {
			
			@Override
			public ILocalProgramVar constructValue(final ILocalProgramVar oldPv) {
				targetScript.lock(this);
				final ILocalProgramVar newPv = (ILocalProgramVar) ProgramVarUtils.transferProgramVar(transferrer,oldPv);
				targetScript.unlock(this);
				return newPv;
			}
		});
		mIProgramNonOldVarCC =
				new ConstructionCache<>(new IValueConstruction<IProgramNonOldVar, IProgramNonOldVar>() {

					@Override
					public IProgramNonOldVar constructValue(final IProgramNonOldVar oldPv) {
						targetScript.lock(this);
						final IProgramNonOldVar newPv = (IProgramNonOldVar) ProgramVarUtils.transferProgramVar(transferrer,oldPv);
						targetScript.unlock(this);
						return newPv;
					}

				});
		mIProgramConstCC = new ConstructionCache<>(oldPv -> {
			final String newIdentifier = oldPv.getIdentifier();
			ApplicationTerm newSmtConstant = (ApplicationTerm) transferrer.transform(oldPv.getDefaultConstant());
			return new ProgramConst(newIdentifier, newSmtConstant, false);
		});
	}

	public ILocalProgramVar getOrConstruct(final ILocalProgramVar key) {
		return mILocalProgramVarCC.getOrConstruct(key);
	}

	public IProgramNonOldVar getOrConstruct(final IProgramNonOldVar key) {
		return mIProgramNonOldVarCC.getOrConstruct(key);
	}

	public IProgramOldVar getOrConstruct(final IProgramOldVar key) {
		return mIProgramNonOldVarCC.getOrConstruct(key.getNonOldVar()).getOldVar();
	}

	public IProgramConst getOrConstruct(final IProgramConst key) {
		return mIProgramConstCC.getOrConstruct(key);
	}

	public Map<ILocalProgramVar, ILocalProgramVar> getILocalProgramVarMap() {
		return Collections.unmodifiableMap(mILocalProgramVarCC);
	}

	public Map<IProgramNonOldVar, IProgramNonOldVar> getIProgramNonOldVarMap() {
		return Collections.unmodifiableMap(mIProgramNonOldVarCC);
	}

	public Map<IProgramConst, IProgramConst> getIProgramConstMap() {
		return Collections.unmodifiableMap(mIProgramConstCC);
	}

	public Map<Term, Term> getIProgramConstTermMap() {
		return getIProgramConstMap().entrySet().stream().collect(
				Collectors.toMap(x -> x.getKey().getDefaultConstant(), x -> x.getValue().getDefaultConstant()));
	}

	public IProgramVar translateProgramVar(final IProgramVar pv) {
		IProgramVar result;
		if (pv instanceof ILocalProgramVar) {
			result = getILocalProgramVarMap().get(pv);
		} else if (pv instanceof IProgramNonOldVar) {
			result = getIProgramNonOldVarMap().get(pv);
		} else if (pv instanceof IProgramOldVar) {
			result = getIProgramNonOldVarMap().get(((IProgramOldVar) pv).getNonOldVar()).getOldVar();
		} else {
			throw new UnsupportedOperationException(pv.getClass().getSimpleName());
		}
		return result;
	}

	public IProgramConst translateProgramConst(final IProgramConst pc) {
		return getIProgramConstMap().get(pc);
	}

}