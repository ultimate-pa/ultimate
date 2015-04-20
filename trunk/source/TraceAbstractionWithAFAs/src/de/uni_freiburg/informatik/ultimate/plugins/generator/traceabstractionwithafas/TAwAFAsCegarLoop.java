package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
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
	
	private int ssaIndex = 10;
	
	private final Map<String, Term> m_IndexedConstants = new HashMap<String, Term>();
	private final Map<BoogieVar, TreeMap<Integer, Term>> m_IndexedVarRepresentative = new HashMap<BoogieVar, TreeMap<Integer, Term>>();

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
			
			/*
			 * intuition for startsOfSubtrees:
			 * the number at position i says where the subtree of the term in the termArray at position i
			 * starts (i.e. diverges from the "lower" branch)
			 */
			ArrayList<Term> termsFromDAG = new ArrayList<>();
			ArrayList<Integer> startsOfSubtreesFromDAG = new ArrayList<>();
			HashMap<BoogieVar, Term> varToSsaVar = new HashMap<>();
			// index for variables that occur for the first time here is 0
			for (BoogieVar bv : dag.getNodeLabel().getBlock().getTransitionFormula().getInVars().keySet())
				if (varToSsaVar.get(bv) == null)
					varToSsaVar.put(bv, buildVersion(bv));
			for (BoogieVar bv : dag.getNodeLabel().getBlock().getTransitionFormula().getOutVars().keySet())
				if (varToSsaVar.get(bv) == null)
					varToSsaVar.put(bv, buildVersion(bv));		
			HashMap<Term, BoogieVar> constantsToBoogieVar = new HashMap<>();

			m_SmtManager.getScript().push(1); //push needs to be here, because getTermsFromDAG declares constants

			getTermsFromDAG(dag, termsFromDAG, startsOfSubtreesFromDAG, 0, varToSsaVar, constantsToBoogieVar);

			//convert ArrayList<Integer> to int[]
			int[] startsOfSubtreesAsInts = new int[startsOfSubtreesFromDAG.size()];
			for (int i = 0; i < startsOfSubtreesFromDAG.size(); i++) {
				startsOfSubtreesAsInts[i] = startsOfSubtreesFromDAG.get(i);
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
						constantsToBoogieVar);
				decorateDagWithInterpolants(dag, predicates);

				AlternatingAutomaton<CodeBlock, IPredicate> alternatingAutomaton = computeAlternatingAutomaton(dag);
				mLogger.info("compute alternating automaton:\n " + alternatingAutomaton);
				assert alternatingAutomaton.accepts(trace) : "interpolant afa does not accept the trace!";
				if (alternatingAutomatonUnion == null) {
					alternatingAutomatonUnion = alternatingAutomaton;
				} else {
					mLogger.debug("merging the following two AFAs:\n" 
							+ "################### 1st AFA: ###################\n"
							+ alternatingAutomatonUnion + "\n"
							+ "################### 2nd AFA: ###################\n"
							+ alternatingAutomaton + "\n");
					AA_MergedUnion<CodeBlock, IPredicate> mergedUnion = 
							new AA_MergedUnion<CodeBlock, IPredicate>(alternatingAutomatonUnion, alternatingAutomaton);
					alternatingAutomatonUnion = mergedUnion.getResult();
					assert checkRAFA(alternatingAutomatonUnion);
				}
				assert alternatingAutomatonUnion.accepts(trace) : "interpolant afa does not accept the trace!";
			} else {
				m_SmtManager.getScript().pop(1);
			}
		}
		mLogger.info(alternatingAutomatonUnion);
		assert alternatingAutomatonUnion.accepts(trace) : "interpolant afa does not accept the trace!";
		//		if (alternatingAutomatonUnion != null) {
		// .. in the end, build the union of all the nwas we got from the
		// dags, return it
		RAFA_Determination<CodeBlock> determination = new RAFA_Determination<CodeBlock>(m_Services, alternatingAutomatonUnion, m_SmtManager, m_PredicateUnifier);
		m_InterpolAutomaton = determination.getResult();
		assert new Accepts<CodeBlock,IPredicate>(m_InterpolAutomaton, (NestedWord<CodeBlock>) trace).getResult() 
			: "interpolant automaton does not accept the trace!";
		//		} else {
//			m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
//				m_Services,
//				m_Abstraction.getAlphabet(),
//				Collections.<CodeBlock>emptySet(),
//				Collections.<CodeBlock>emptySet(),
//				m_Abstraction.getStateFactory()
//			);
//		}
	}
	
	private Word<CodeBlock> reverse(Word<CodeBlock> trace) {
		CodeBlock[] newWord = new CodeBlock[trace.length()];
		int[] newNestingRelation = new int[trace.length()];
		for (int i = 0; i < trace.length(); i++) {
			newWord[trace.length() - 1 - i] = trace.getSymbol(i);
			newNestingRelation[i] = -2;
		}
		return new NestedWord<CodeBlock>(newWord, newNestingRelation);
	}

	/**
	 * Given DataflowDAG dag, go through it in postorder and add the Terms of the Dagnodes' transition formulas
	 * to a term list. Save the nesting in an int array (every entry points to the branching point of its subtree).
	 * Also maintains a special SSA-renaming suited for DataflowDAGs (i.e. duplicated statements in the tree need
	 * to have unique variables)
	 */
	private void getTermsFromDAG(DataflowDAG<TraceCodeBlock> dag, ArrayList<Term> terms,
			ArrayList<Integer> startsOfSubtrees, int currentSubtree, HashMap<BoogieVar,Term> varToSsaVar,
			HashMap<Term,BoogieVar> constantsToBoogieVar) {
		
		HashMap<BoogieVar,Term> varToSsaVarNew = new HashMap<>(varToSsaVar);//copy (nice would be immutable maps)
		BoogieVar writtenVar = null;
		Term writtenVarSsa = null;

			//do nothing -- all the ssa-versions stay the same in an assume
//		} else {
			//only the ssa-version of the variable that is on the write-edge of this node is used in this 
			//node's ssa. 
			//All the other nodes get a fresh SSA-version
			assert dag.getIncomingNodes().size() <= 1 : "DataflowDAG is not a tree, expecting a tree";
			writtenVar = dag.getIncomingNodes().size() == 1 ?
							dag.getIncomingEdgeLabel(dag.getIncomingNodes().get(0)).getBoogieVar() :
								null;
			writtenVarSsa = varToSsaVar.get(writtenVar);

			for (BoogieVar bv : dag.getNodeLabel().getBlock().getTransitionFormula().getInVars().keySet())
				varToSsaVarNew.put(bv, buildVersion(bv));
			for (BoogieVar bv : dag.getNodeLabel().getBlock().getTransitionFormula().getOutVars().keySet())
				varToSsaVarNew.put(bv, buildVersion(bv));
		if (dag.getNodeLabel().getBlock().getTransitionFormula().getAssignedVars().isEmpty()) {
			//in case of an assume, the variable on the incoming edge 
			//(i.e. the variable that is counted as written by this node's statement)
			//keeps its old version
			varToSsaVarNew.put(writtenVar, writtenVarSsa);
		}
		
		for (int i = 0; i < dag.getOutgoingNodes().size(); i++) {
			DataflowDAG<TraceCodeBlock> outNode = dag.getOutgoingNodes().get(i);
			getTermsFromDAG(outNode, 
					terms, 
					startsOfSubtrees, i == 0 ? currentSubtree : terms.size(), 
					varToSsaVarNew, constantsToBoogieVar);
		}
		terms.add(computeSsaTerm(dag.getNodeLabel(), writtenVar, writtenVarSsa, varToSsaVarNew, constantsToBoogieVar));
		startsOfSubtrees.add(currentSubtree);
	}

	/**
	 * varToIndexOld has the versioning for the outvars, varToIndexNew has the versioning for the invars
	 * (it is that way around essentially because we go from root to leaf in the DataFlowDAG)
	 */
	private Term computeSsaTerm(TraceCodeBlock nodeLabel,
//			HashMap<BoogieVar,Term> varToSsaVarOld, 
			BoogieVar writtenVar, Term writtenVarSsa,
			HashMap<BoogieVar,Term> varToSsaVarNew, HashMap<Term,BoogieVar> constantsToBoogieVar) {
		TransFormula transFormula = nodeLabel.getBlock().getTransitionFormula();
	
		Map<TermVariable, Term> substitutionMapping = new HashMap<TermVariable, Term>();

		for (Entry<BoogieVar, TermVariable> entry : transFormula.getInVars().entrySet()) {
            Term t = varToSsaVarNew.get(entry.getKey());
            assert t != null;
			substitutionMapping.put(entry.getValue(), t);
			constantsToBoogieVar.put((ApplicationTerm) t, entry.getKey());
		}
		for (Entry<BoogieVar, TermVariable> entry : transFormula.getOutVars().entrySet()) {
			Term t = null;
			if (writtenVar != null  
					&& entry.getKey().equals(writtenVar)) { 
				t = writtenVarSsa;
			} else { // if writtenVar is null (when we are at the tree's root), just take the value from the map
				t = varToSsaVarNew.get(entry.getKey());
			}
            assert t != null;
			substitutionMapping.put(entry.getValue(), t);
			constantsToBoogieVar.put((ApplicationTerm) t, entry.getKey());
		}
		
		Term substitutedTerm = (new Substitution(substitutionMapping, m_SmtManager.getScript()))
				.transform(nodeLabel.getBlock().getTransitionFormula().getFormula());
		return substitutedTerm;
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
		alternatingAutomaton.addAcceptingConjunction(alternatingAutomaton.generateCube(new IPredicate[]{initialState}, new IPredicate[0]));

		IHoareTripleChecker mhtc = new MonolithicHoareTripleChecker(m_SmtManager);//TODO: switch to efficient htc later, perhaps

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
					alternatingAutomaton.generateCube(targetStates.toArray(new IPredicate[targetStates.size()]), new IPredicate[0])
				);
				assert mhtc.checkInternal(
						m_SmtManager.newPredicate(m_SmtManager.and(targetStates.toArray(new IPredicate[targetStates.size()]))),
						currentDag.getNodeLabel().getBlock(),
						currentDag.getNodeLabel().getInterpolant()) == Validity.VALID;
			}
			else{
				alternatingAutomaton.addTransition(
					currentDag.getNodeLabel().getBlock(),
					currentDag.getNodeLabel().getInterpolant(),
					alternatingAutomaton.generateCube(new IPredicate[]{finalState}, new IPredicate[0])
				);
				assert mhtc.checkInternal(
						m_SmtManager.newPredicate(m_SmtManager.and(targetStates.toArray(new IPredicate[targetStates.size()]))),
						currentDag.getNodeLabel().getBlock(),
						currentDag.getNodeLabel().getInterpolant()) == Validity.VALID;
			}
		}

		//Add transitions according to hoare triples
		IHoareTripleChecker htc = getEfficientHoareTripleChecker();
		for(CodeBlock letter : alternatingAutomaton.getAlphabet()){
			for(IPredicate sourceState : alternatingAutomaton.getStates()){
//				if(sourceState == m_PredicateUnifier.getFalsePredicate()){
//					continue;
//				}
				for(IPredicate targetState : alternatingAutomaton.getStates()){
//					if(targetState == m_PredicateUnifier.getTruePredicate()){
//						continue;
//					}
					if (htc.checkInternal(sourceState, letter, targetState) == Validity.VALID) {
						alternatingAutomaton.addTransition(
							letter,
							targetState,
							alternatingAutomaton.generateCube(new IPredicate[]{sourceState}, new IPredicate[0])
						);
					}
				}
			}
		}
		alternatingAutomaton.setReversed(true);
		assert checkRAFA(alternatingAutomaton);
		return alternatingAutomaton;
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
		assert !stillAccepted : "stillAccepted --> no progress";
		return !stillAccepted;
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
	
	/**
	 * Computes the DNF belonging to the given BooleanExpression and Statelist as an IPredicate
	 * Helper method for assertions.
	 */
	IPredicate bexToPredicate(BooleanExpression bex, List<IPredicate> states) {
		IPredicate pred = m_PredicateUnifier.getTruePredicate();
		for(int i = 0; i < states.size(); i++){
			if(bex.getAlpha().get(i)){
				pred = m_SmtManager.newPredicate(
						m_SmtManager.and(pred,
								!bex.getBeta().get(i) ?
									m_SmtManager.newPredicate(m_SmtManager.not(states.get(i))) :
										states.get(i)));
			}
		}
		if(bex.getNextConjunctExpression() != null){
			pred = m_SmtManager.newPredicate(m_SmtManager.or(pred, 
					bexToPredicate(bex.getNextConjunctExpression(), states)));
		}
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
	
	int getFreshSsaIndex() {
		return ssaIndex++;
	}
	
	/**
	 * Build constant bv_index that represents BoogieVar bv that obtains a new
	 * value at position index.
	 */
//	private Term buildVersion(BoogieVar bv, int index) {
	private Term buildVersion(BoogieVar bv) {
		int index = getFreshSsaIndex();
		TreeMap<Integer, Term> index2constant = m_IndexedVarRepresentative.get(bv);
		if (index2constant == null) {
			index2constant = new TreeMap<Integer, Term>();
			m_IndexedVarRepresentative.put(bv, index2constant);
		}
		assert !index2constant.containsKey(index) : "version was already constructed";

		Term constant = PredicateUtils.getIndexedConstant(bv, index, m_IndexedConstants, m_SmtManager.getScript());
//		Term constant = PredicateUtils.getIndexedConstant(bv, index, new HashMap<String,Term>(), m_SmtManager.getScript());
		index2constant.put(index, constant);
		return constant;
	}
}
