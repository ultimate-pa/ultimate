package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import org.apache.log4j.Level;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AA_MergedUnion;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.BooleanExpression;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaWalker;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.ReachingDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.TraceCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateConstructionVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.CegarLoopConcurrentAutomata;

/*
 * plan:
 * - von CegarLoopConcurrent erben
 *  --> Produktautomat aus einem parallelen Programm wird automatisch gebaut
 * - computeInterpolantAutomaton �berschreiben
 * - "Powerset" Einstellung f�r refine abstraction w�hlen
 */
//

public class TAwAFAsCegarLoop extends CegarLoopConcurrentAutomata {

	private PredicateUnifier m_PredicateUnifier;
	private TraceCheckerWithAccessibleSSATerms m_traceCheckerWAST = null; 

	public TAwAFAsCegarLoop(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks traceAbstractionBenchmarks, TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs, INTERPOLATION interpolation, boolean computeHoareAnnotation,
			IUltimateServiceProvider services, IToolchainStorage storage) {
		super(name, rootNode, smtManager, traceAbstractionBenchmarks, taPrefs, errorLocs, services, storage);
		m_PredicateUnifier = new PredicateUnifier(services, smtManager, smtManager.newTruePredicate(),
				smtManager.newFalsePredicate());
	}

	private List<DataflowDAG<TraceCodeBlock>> testReachDef() throws AssertionError {
		try {
			List<CodeBlock> word = m_Counterexample.getWord().asList();
			StringBuilder sb = new StringBuilder();
			for (CodeBlock letter : word) {
				sb.append("[").append(letter).append("] ");
			}
			Level old = mLogger.getLevel();
			mLogger.setLevel(Level.DEBUG);
			mLogger.debug("Calculating RD DAGs for " + sb);
			List<DataflowDAG<TraceCodeBlock>> dags = ReachingDefinitions.computeRDForTrace(word, mLogger, m_RootNode);
			mLogger.setLevel(old);
			return dags;
		} catch (Throwable e) {
			mLogger.fatal("DataflowDAG generation threw an exception.", e);
			throw new AssertionError();
		}
	}

	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		Word<CodeBlock> trace = m_traceCheckerWAST.getTrace();
		mLogger.debug("current trace:");
		mLogger.debug(trace.toString());

		List<DataflowDAG<TraceCodeBlock>> dags = testReachDef();

		AlternatingAutomaton<CodeBlock, IPredicate> alternatingAutomatonUnion = null;
		for (DataflowDAG<TraceCodeBlock> dag : dags) {
			ArrayList<Term> termsFromDAG = new ArrayList<>();
			ArrayList<Integer> startsOfSubtreesFromDAG = new ArrayList<>();
			getTermsFromDAG(dag, termsFromDAG, startsOfSubtreesFromDAG, 0);

			int[] startsOfSubtreesAsInts = new int[startsOfSubtreesFromDAG.size()];
			for (int i = 0; i < startsOfSubtreesFromDAG.size(); i++) {
				startsOfSubtreesAsInts[i] = startsOfSubtreesFromDAG.get(i);
			}

			m_SmtManager.getScript().push(1);
			// declare all variables (all would not be necessary, but well..
			for (Term t : m_traceCheckerWAST.getConstantsToBoogieVar().keySet()) {
				ApplicationTerm at = (ApplicationTerm) t;
				m_SmtManager.getScript().declareFun(at.getFunction().getName(), new Sort[0], at.getSort());
			}

			// assert the terms for the current dag, name them
			ArrayList<Term> termNames = new ArrayList<Term>();
			for (int i = 0; i < termsFromDAG.size(); i++) {
				String termName = "afassa_" + i;
				m_SmtManager.assertTerm(m_SmtManager.getScript().annotate(termsFromDAG.get(i),
						new Annotation(":named", termName)));
				termNames.add(m_SmtManager.getScript().term(termName));
			}

			// if the conjunctions of the terms in the current dag is infeasible..
			if (m_SmtManager.getScript().checkSat() == LBool.UNSAT) {
				// .. compute tree interpolant for the current dag
				Term[] interpolants = m_SmtManager.getScript().getInterpolants(
						termNames.toArray(new Term[termNames.size()]), startsOfSubtreesAsInts);
				m_SmtManager.getScript().pop(1);
				IPredicate[] predicates = interpolantsToPredicates(interpolants,
						m_traceCheckerWAST.getConstantsToBoogieVar());
				decorateDagWithInterpolants(dag, predicates);

				// TODO: what about converting the dag to a tree??
				AlternatingAutomaton<CodeBlock, IPredicate> alternatingAutomaton = computeAlternatingAutomaton(dag);
				mLogger.debug("compute alternating automaton:\n " + alternatingAutomaton);
				if (alternatingAutomatonUnion == null) {
					alternatingAutomatonUnion = alternatingAutomaton;
				} else {
					AA_MergedUnion<CodeBlock, IPredicate> mergedUnion = new AA_MergedUnion<CodeBlock, IPredicate>(alternatingAutomatonUnion, alternatingAutomaton);
					alternatingAutomatonUnion = mergedUnion.getResult();
					assert checkRAFA(alternatingAutomatonUnion);
				}
				// in the future:
				// - reverse and _determinize_ in one step
				// - perhaps use conjunction of predicates instead of
				// CompoundState
				// - make use of the fact that afas are easy to complement??
				// - do union operation on r-AFAs??
			} else {
				m_SmtManager.getScript().pop(1);
			}
		}
		mLogger.info(alternatingAutomatonUnion);
		if (alternatingAutomatonUnion != null) {
			// .. in the end, build the union of all the nwas we got from the
			// dags, return it
			RAFA_Determination<CodeBlock> determination = new RAFA_Determination<CodeBlock>(m_Services, alternatingAutomatonUnion, m_SmtManager, m_PredicateUnifier);
			m_InterpolAutomaton = determination.getResult();
		} else {
			m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_Services,
				m_Abstraction.getAlphabet(),
				Collections.<CodeBlock>emptySet(),
				Collections.<CodeBlock>emptySet(),
				m_Abstraction.getStateFactory()
			);
		}
	}

	private void decorateDagWithInterpolants(DataflowDAG<TraceCodeBlock> dag, IPredicate[] interpolants) {
		Stack<DataflowDAG<TraceCodeBlock>> stack = new Stack<>();
		stack.push(dag);

		int currentInterpolantIndex = interpolants.length - 1;

		DataflowDAG<TraceCodeBlock> currentNode = null;

		while (!stack.isEmpty()) {
			currentNode = stack.pop();
			mLogger.debug("visiting node " + currentNode.getNodeLabel().toString());
			if (currentNode == dag) { // for the root we take "false"
				currentNode.getNodeLabel().addInterpolant(m_PredicateUnifier.getFalsePredicate());
			} else {
				currentNode.getNodeLabel().addInterpolant(
						interpolants[currentInterpolantIndex]);
				currentInterpolantIndex--;
			}
			stack.addAll(currentNode.getOutgoingNodes());
		}
	}

	private IPredicate[] interpolantsToPredicates(Term[] interpolants, Map<Term, BoogieVar> constants2BoogieVar) {
		IPredicate[] result = new IPredicate[interpolants.length];
		PredicateConstructionVisitor m_sfmv = new PredicateConstructionVisitor(constants2BoogieVar);

		SafeSubstitution const2RepTvSubst;

		HashMap<Term, Term> const2RepTv = new HashMap<Term, Term>();
		for (Entry<Term, BoogieVar> entry : constants2BoogieVar.entrySet()) {
			const2RepTv.put(entry.getKey(), entry.getValue().getTermVariable());
		}

		const2RepTvSubst = new SafeSubstitution(m_SmtManager.getScript(), const2RepTv);
		Map<Term, IPredicate> withIndices2Predicate = new HashMap<Term, IPredicate>();

		int craigInterpolPos = 0;
		for (int resultPos = 0; resultPos < interpolants.length; resultPos++) {
			Term withIndices = interpolants[craigInterpolPos];
			craigInterpolPos++;
			result[resultPos] = withIndices2Predicate.get(withIndices);
			if (result[resultPos] == null) {
				m_sfmv.clearVarsAndProc();
				Term withoutIndices = const2RepTvSubst.transform(withIndices);
				TermVarsProc tvp = TermVarsProc.computeTermVarsProc(withoutIndices, m_SmtManager.getBoogie2Smt());
				result[resultPos] = m_PredicateUnifier.getOrConstructPredicate(tvp);
				withIndices2Predicate.put(withIndices, result[resultPos]);
			}
		}
		assert craigInterpolPos == interpolants.length;
		return result;
	}

	private AlternatingAutomaton<CodeBlock, IPredicate> computeAlternatingAutomaton(DataflowDAG<TraceCodeBlock> dag){
		AlternatingAutomaton<CodeBlock, IPredicate> alternatingAutomaton = new AlternatingAutomaton<CodeBlock, IPredicate>(m_Abstraction.getAlphabet(), m_Abstraction.getStateFactory());
		IPredicate initialState = m_PredicateUnifier.getFalsePredicate();
		IPredicate finalState = m_PredicateUnifier.getTruePredicate();
		alternatingAutomaton.addState(initialState);
		alternatingAutomaton.addState(finalState);
		alternatingAutomaton.setStateFinal(finalState);
		alternatingAutomaton.addAcceptingConjunction(alternatingAutomaton.generateDisjunction(new IPredicate[]{initialState}, new IPredicate[0]));

//		IHoareTripleChecker htc = new MonolithicHoareTripleChecker(m_SmtManager);//TODO: switch to efficient htc later, perhaps
		IHoareTripleChecker htc = getEfficientHoareTripleChecker();

		//Build the automaton according to the structure of the DAG
		Stack<DataflowDAG<TraceCodeBlock>> stack = new Stack<DataflowDAG<TraceCodeBlock>>();
		stack.push(dag);
		while(!stack.isEmpty()){
			DataflowDAG<TraceCodeBlock> currentDag = stack.pop();
			HashSet<IPredicate> targetStates = new HashSet<IPredicate>();
			for(DataflowDAG<TraceCodeBlock> outNode : currentDag.getOutgoingNodes()){
				IPredicate outNodePred = outNode.getNodeLabel().getInterpolant();
				alternatingAutomaton.addState(outNodePred);
				targetStates.add(outNodePred);
				stack.push(outNode);
			}
			if(!targetStates.isEmpty()){
				alternatingAutomaton.addTransition(
					currentDag.getNodeLabel().getBlock(),
					currentDag.getNodeLabel().getInterpolant(),
					alternatingAutomaton.generateDisjunction(targetStates.toArray(new IPredicate[targetStates.size()]), new IPredicate[0])
				);
//				assert htc.checkInternal(
//						m_SmtManager.newPredicate(m_SmtManager.and(targetStates.toArray(new IPredicate[targetStates.size()]))),
//						currentDag.getNodeLabel().getBlock(),
//						currentDag.getNodeLabel().getInterpolant()) == Validity.VALID;
			}
			else{
				alternatingAutomaton.addTransition(
					currentDag.getNodeLabel().getBlock(),
					currentDag.getNodeLabel().getInterpolant(),
					alternatingAutomaton.generateDisjunction(new IPredicate[]{finalState}, new IPredicate[0])
				);
//				assert htc.checkInternal(
//						m_SmtManager.newPredicate(m_SmtManager.and(targetStates.toArray(new IPredicate[targetStates.size()]))),
//						currentDag.getNodeLabel().getBlock(),
//						currentDag.getNodeLabel().getInterpolant()) == Validity.VALID;
			}
		}

		//Add transitions according to hoare triples
		for(CodeBlock letter : alternatingAutomaton.getAlphabet()){
			for(IPredicate sourceState : alternatingAutomaton.getStates()){
				if(sourceState == m_PredicateUnifier.getFalsePredicate()){
					continue;
				}
				for(IPredicate targetState : alternatingAutomaton.getStates()){
					if(targetState == m_PredicateUnifier.getTruePredicate()){
						continue;
					}
					if (htc.checkInternal(sourceState, letter, targetState) == Validity.VALID) {
						alternatingAutomaton.addTransition(
							letter,
							targetState,
							alternatingAutomaton.generateDisjunction(new IPredicate[]{sourceState}, new IPredicate[0])
						);
					}
				}
			}
		}
		alternatingAutomaton.setReversed(true);
		assert checkRAFA(alternatingAutomaton);
		return alternatingAutomaton;
	}

	private void getTermsFromDAG(DataflowDAG<TraceCodeBlock> dag, ArrayList<Term> terms,
			ArrayList<Integer> startsOfSubtrees, int currentSubtree) {
		for (int i = 0; i < dag.getOutgoingNodes().size(); i++) {
			DataflowDAG<TraceCodeBlock> outNode = dag.getOutgoingNodes().get(i);
			getTermsFromDAG(outNode, terms, startsOfSubtrees, i == 0 ? currentSubtree : terms.size());
		}
		terms.add(m_traceCheckerWAST.getSSATerm(dag.getNodeLabel().getIndex()));
		startsOfSubtrees.add(currentSubtree);
	}

	@Override
	protected LBool isCounterexampleFeasible() {
		PredicateUnifier predicateUnifier = new PredicateUnifier(m_Services, m_SmtManager);
		IPredicate truePredicate = predicateUnifier.getTruePredicate();
		IPredicate falsePredicate = predicateUnifier.getFalsePredicate();

		switch (m_Interpolation) {
		case Craig_TreeInterpolation:
			m_traceCheckerWAST = new TraceCheckerWithAccessibleSSATerms(truePredicate, falsePredicate,
					new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(m_Counterexample.getWord()),
					m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager(), m_AssertCodeBlocksIncrementally,
					m_Services, true, predicateUnifier, m_Interpolation);
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		LBool feasibility = m_traceCheckerWAST.isCorrect();
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(m_Counterexample.getWord());
			String indentation = "";
			indentation += "  ";
			for (int j = 0; j < counterexample.length(); j++) {
				if (counterexample.isCallPosition(j)) {
					indentation += "    ";
				}
				if (counterexample.isReturnPosition(j)) {
					indentation = indentation.substring(0, indentation.length() - 4);
				}
			}
			m_RcfgProgramExecution = m_traceCheckerWAST.getRcfgProgramExecution();
		}
		m_traceCheckerWAST.traceCheckFinished();
		m_CegarLoopBenchmark.addTraceCheckerData(m_traceCheckerWAST.getTraceCheckerBenchmark());

		return feasibility;
	}
	
	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException { //copied
		m_StateFactoryForRefinement.setIteration(super.m_Iteration);

		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AutomataDifference);
		boolean explointSigmaStarConcatOfIA = !m_ComputeHoareAnnotation;

		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		IHoareTripleChecker htc = this.getEfficientHoareTripleChecker(); //change to CegarLoopConcurrentAutomata
		mLogger.debug("Start constructing difference");
		assert (oldAbstraction.getStateFactory() == m_InterpolAutomaton.getStateFactory());

		IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

		DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(
				m_Services, m_SmtManager, m_ModGlobVarManager, htc, oldAbstraction, m_InterpolAutomaton,
				this.m_PredicateUnifier, mLogger, false);//change to CegarLoopConcurrentAutomata
		// ComplementDeterministicNwa<CodeBlock, IPredicate>
		// cdnwa = new ComplementDeterministicNwa<>(dia);
		PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
				determinized, false, m_PredicateFactoryInterpolantAutomata);

		if (m_Pref.differenceSenwa()) {
			diff = new DifferenceSenwa<CodeBlock, IPredicate>(m_Services, oldAbstraction, (INestedWordAutomaton<CodeBlock, IPredicate>) determinized, psd2, false);
		} else {
			diff = new Difference<CodeBlock, IPredicate>(m_Services, oldAbstraction, determinized, psd2,
					m_StateFactoryForRefinement, explointSigmaStarConcatOfIA);
		}
		assert !m_SmtManager.isLocked();
		assert (new InductivityCheck(m_Services, m_InterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager))).getResult();
		// do the following check only to obtain logger messages of
		// checkInductivity

		if (m_RemoveDeadEnds) {
			if (m_ComputeHoareAnnotation) {
				Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
				m_Haf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
			}
			diff.removeDeadEnds();
			if (m_ComputeHoareAnnotation) {
				m_Haf.addDeadEndDoubleDeckers(diff);
			}
		}

		m_Abstraction = (IAutomaton<CodeBlock, IPredicate>) diff.getResult();
		// m_DeadEndRemovalTime = diff.getDeadEndRemovalTime();
		if (m_Pref.dumpAutomata()) {
			String filename = "InterpolantAutomaton_Iteration" + m_Iteration;
			super.writeAutomatonToFile(m_InterpolAutomaton, filename);
		}

		m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataDifference);

		Minimization minimization = m_Pref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			minimizeAbstraction(m_StateFactoryForRefinement, m_PredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}

		boolean stillAccepted = (new Accepts<CodeBlock, IPredicate>(
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction,
				(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
		if (stillAccepted) {
			return false;
		} else {
			return true;
		}
	}
	
	
	protected IHoareTripleChecker getEfficientHoareTripleChecker() //copied
			throws AssertionError {
		final IHoareTripleChecker solverHtc;
		switch (m_Pref.getHoareTripleChecks()) {
		case MONOLITHIC:
			solverHtc = new MonolithicHoareTripleChecker(m_SmtManager);
			break;
		case INCREMENTAL:
			solverHtc = new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager);
			break;
		default:
			throw new AssertionError("unknown value");
		}
		IHoareTripleChecker htc = new EfficientHoareTripleChecker(solverHtc, 
				m_RootNode.getRootAnnot().getModGlobVarManager(), 
				this.m_PredicateUnifier, m_SmtManager); //only change to method in BasicCegarLoop
		return htc;
	}
	
	IPredicate bexToPredicate(BooleanExpression bex, List<IPredicate> states) {
//		String text = "";
		IPredicate pred = m_PredicateUnifier.getTruePredicate();
//		int r = 0;
		for(int i = 0; i < states.size(); i++){
//			if(alpha.get(i)){
//				if(r != 0){
//					text += " ^ ";
//				}
//				if(!beta.get(i)){
//					text += "~";
//				}
//				text += variables.get(i);
//				r++;
//			}

			if(bex.getAlpha().get(i)){
				pred = m_SmtManager.newPredicate(
						m_SmtManager.and(pred,
								!bex.getBeta().get(i) ?
									m_SmtManager.newPredicate(m_SmtManager.not(states.get(i))) :
										states.get(i)
						));
			}
		}
		if(bex.getNextConjunctExpression() != null){
//			if(r > 1){
//				text = "(" + text + ")";
//			}
//			text += " v " + nextConjunctExpression.toString(variables);
			pred = m_SmtManager.newPredicate(m_SmtManager.or(pred, 
					bexToPredicate(bex.getNextConjunctExpression(), states)));
		}
//		return text;
		return pred;
	}

	/**
	 * return true if the input reversed afa has the properties we wish for
	 * those properties are:
	 *  - the corresponding hoare triple of each transition is valid
	 */
	private boolean checkRAFA(AlternatingAutomaton<CodeBlock, IPredicate> afa) {
		MonolithicHoareTripleChecker htc = new MonolithicHoareTripleChecker(m_SmtManager);
		boolean result = true;
		for (Entry<CodeBlock, BooleanExpression[]> entry : afa.getTransitionFunction().entrySet()) {
			for(int i=0;i<afa.getStates().size();i++){
				if(entry.getValue()[i] != null){
//					text += "\t\t\t" + states.get(i) + " => " + entry.getValue()[i].toString(states);
					IPredicate pre = bexToPredicate(entry.getValue()[i], afa.getStates());
					IPredicate succ = afa.getStates().get(i);
					boolean check = htc.checkInternal(pre, entry.getKey(), succ) == Validity.VALID;
					result &= check;
					if (!check)
						mLogger.warn("the following non-inductive transition occurs in the current AFA:\n"
								+ "pre: " + pre + "\n"
								+ "stm: " + entry.getKey() + "\n"
								+ "succ: " + succ
								);

				}
			}
		}
		return result;
	}
}
