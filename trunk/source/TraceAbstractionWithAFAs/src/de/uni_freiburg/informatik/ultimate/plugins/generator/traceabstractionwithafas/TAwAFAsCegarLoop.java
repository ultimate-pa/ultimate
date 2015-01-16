package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AA_Union;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.TestAutomaton_1;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaWalker;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.ReachingDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.TraceCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateConstructionVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.CegarLoopConcurrentAutomata;

/*
 * plan:
 * - von CegarLoopConcurrent erben
 *  --> Produktautomat aus einem parallelen Programm wird automatisch gebaut
 * - computeInterpolantAutomaton überschreiben
 * - "Powerset" Einstellung für refine abstraction wählen
 */
//

public class TAwAFAsCegarLoop extends CegarLoopConcurrentAutomata {

	private final BoogieSymbolTable mSymbolTable;
	private PredicateUnifier mPredicateUnifier;
	private TraceCheckerWithAccessibleSSATerms traceCheckerWAST = null; //TODO move this declaration up
	private Logger m_Logger;

	public TAwAFAsCegarLoop(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks traceAbstractionBenchmarks, TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs, INTERPOLATION interpolation, boolean computeHoareAnnotation,
			IUltimateServiceProvider services, BoogieSymbolTable table) {
		super(name, rootNode, smtManager, traceAbstractionBenchmarks, taPrefs, errorLocs, services);
		assert table != null;
		mSymbolTable = table;
		mPredicateUnifier = new PredicateUnifier(services, smtManager, smtManager.newTruePredicate(), smtManager.newFalsePredicate());
		m_Logger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}


	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		traceCheckerWAST = (TraceCheckerWithAccessibleSSATerms) m_TraceChecker;

		Word<CodeBlock> trace = traceCheckerWAST.getTrace();
		mLogger.debug("current trace:");
		mLogger.debug(trace.toString());
		traceCheckerWAST.finishTraceCheckWithoutInterpolantsOrProgramExecution();

		List<DataflowDAG<TraceCodeBlock>> dags = null;
		try{
			dags = ReachingDefinitions.computeRDForTrace(trace.asList(), mLogger, mSymbolTable);
		}catch(Throwable e){
			mLogger.fatal("DataflowDAG generation threw an exception.", e);
		}

		AlternatingAutomaton<CodeBlock, IPredicate> alternatingAutomatonUnion = null;
		for(DataflowDAG<TraceCodeBlock> dag : dags){
			ArrayList<Term> termsFromDAG = new ArrayList<>();
			ArrayList<Integer> startsOfSubtreesFromDAG = new ArrayList<>();
			getTermsFromDAG(dag, termsFromDAG, startsOfSubtreesFromDAG, 0);

			int[] startsOfSubtreesAsInts = new int[startsOfSubtreesFromDAG.size()];
			for(int i=0;i<startsOfSubtreesFromDAG.size();i++){
				startsOfSubtreesAsInts[i] = startsOfSubtreesFromDAG.get(i);
			}

			m_SmtManager.getScript().push(1);
			//declare all variables (all would not be necessary, but well..
			for (Term t : traceCheckerWAST.getConstantsToBoogieVar().keySet()) {
				ApplicationTerm at = (ApplicationTerm) t;
				m_SmtManager.getScript().declareFun(at.getFunction().getName(), new Sort[0], at.getSort());
			}

			//assert the terms for the current dag, name them
			ArrayList<Term> termNames = new ArrayList<Term>();
			for(int i=0;i<termsFromDAG.size();i++){
				String termName = "afassa_" + i;
				m_SmtManager.assertTerm(m_SmtManager.getScript().annotate(termsFromDAG.get(i), new Annotation(":named", termName)));
				termNames.add(m_SmtManager.getScript().term(termName));
			}

			//if the conjunctions of the terms in the current dag is infeasible..
			mLogger.info(dag + "\t" + m_SmtManager.getScript().checkSat());
			if(m_SmtManager.getScript().checkSat() == LBool.UNSAT){
				//.. compute tree interpolant for the current dag
				Term[] interpolants = m_SmtManager.getScript().getInterpolants(termNames.toArray(new Term[termNames.size()]), startsOfSubtreesAsInts);
				m_SmtManager.getScript().pop(1);
				IPredicate[] predicates = interpolantsToPredicates(interpolants, traceCheckerWAST.getConstantsToBoogieVar());
				decorateDagWithInterpolants(dag, predicates);
				
				//TODO: what about converting the dag to a tree??
				AlternatingAutomaton<CodeBlock, IPredicate> alternatingAutomaton = computeAlternatingAutomaton(dag);
				mLogger.debug("compute alternating automaton:\n " + alternatingAutomaton);
				if(alternatingAutomatonUnion == null){
					alternatingAutomatonUnion = alternatingAutomaton;
				}
				else{
					AA_Union<CodeBlock, IPredicate> union = new AA_Union<CodeBlock, IPredicate>(alternatingAutomatonUnion, alternatingAutomaton);
					alternatingAutomatonUnion = union.getResult();
				}
				//in the future: 
				// - reverse and _determinize_ in one step
				// - perhaps use conjunction of predicates instead of CompoundState
				// - make use of the fact that afas are easy to complement??
				// - do union operation on r-AFAs??
			}
			else{
				m_SmtManager.getScript().pop(1);
			}
		}
		if(alternatingAutomatonUnion != null){
			//.. in the end, build the union of all the nwas we got from the dags, return it
			AA_Determination<CodeBlock> determination = new AA_Determination<CodeBlock>(m_Services, alternatingAutomatonUnion, m_SmtManager, mPredicateUnifier);
			m_InterpolAutomaton = determination.getResult();
		}
		else{
			m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_Services,
				m_Abstraction.getAlphabet(),
				Collections.<CodeBlock>emptySet(),
				Collections.<CodeBlock>emptySet(),
				m_Abstraction.getStateFactory()
			);
		}
		// super.constructInterpolantAutomaton();
	}

	private void decorateDagWithInterpolants(DataflowDAG<TraceCodeBlock> dag,
			IPredicate[] interpolants) {
		Stack<DataflowDAG<TraceCodeBlock>> stack = new Stack<>();
		stack.push(dag);

		int currentInterpolantIndex = interpolants.length - 1;

		DataflowDAG<TraceCodeBlock> currentNode = null;

		while(!stack.isEmpty()) {
			currentNode = stack.pop();
			mLogger.debug("visiting node " + currentNode.getNodeLabel().toString());
			if (currentNode == dag) { //for the root we take "false"
				currentNode.getNodeLabel().addInterpolant(mPredicateUnifier.getFalsePredicate());
			} else {
				//				if (currentNode.getOutgoingNodes().size() > 0) {
				currentNode.getNodeLabel().addInterpolant(
						//							mPredicateUnifier.
						//							getOrConstructPredicate(
						//									TermVarsProc.computeTermVarsProc(interpolants[currentInterpolantIndex],
						//											this.m_RootNode.getRootAnnot().getBoogie2SMT())));			
						interpolants[currentInterpolantIndex]);
				currentInterpolantIndex--;
				//				} else {
				//					currentNode.getNodeLabel().addInterpolant(mPredicateUnifier.getTruePredicate());
				//				}
			}

			stack.addAll(currentNode.getOutgoingNodes());
		}

	}


	private IPredicate[] interpolantsToPredicates(Term[] interpolants, 
			Map<Term, BoogieVar> constants2BoogieVar) {//copied from NestedSSABuilder
		IPredicate[] result = new IPredicate[interpolants.length];
		//		assert m_CraigInterpolants.length == craigInt2interpolantIndex.size();
		// assert m_InterpolatedPositions.size() == m_CraigInterpolants.length;
		PredicateConstructionVisitor m_sfmv = new PredicateConstructionVisitor(constants2BoogieVar);
		FormulaWalker walker = new FormulaWalker(m_sfmv, m_SmtManager.getScript());

		Map<Term, IPredicate> withIndices2Predicate = new HashMap<Term, IPredicate>();

		int craigInterpolPos = 0;
		for (int resultPos = 0; resultPos < interpolants.length; resultPos++) {
			int positionOfThisCraigInterpolant = resultPos;
			//			if (craigInterpolPos == m_CraigInterpolants.length) {
			//				// special case where trace ends with return
			//				// we already added all CraigInterpolants
			//				// remaining interpolants are "unknown" and the implicit given
			//				// false at the end
			//				assert m_Trace.isReturnPosition(m_Trace.length() - 1);
			//				positionOfThisCraigInterpolant = Integer.MAX_VALUE;
			//			} else {
			//				positionOfThisCraigInterpolant = craigInt2interpolantIndex.get(craigInterpolPos);
			//			}
			//			assert positionOfThisCraigInterpolant >= resultPos;
			//			if (isInterpolatedPositio(resultPos)) {
			Term withIndices = interpolants[craigInterpolPos];
			//				assert resultPos == craigInt2interpolantIndex.get(craigInterpolPos);
			craigInterpolPos++;
			result[resultPos] = withIndices2Predicate.get(withIndices);
			if (result[resultPos] == null) {
				m_sfmv.clearVarsAndProc();
				Term withoutIndices = walker.process(new FormulaUnLet().unlet(withIndices));
				Set<BoogieVar> vars = m_sfmv.getVars();
				String[] procs = m_sfmv.getProcedure().toArray(new String[0]);
				result[resultPos] = mPredicateUnifier.getOrConstructPredicate(withoutIndices, vars, procs);
				withIndices2Predicate.put(withIndices, result[resultPos]);
			}
			//			} else {
			//				result[resultPos] = m_SmtManager.newDontCarePredicate(null);
			//			}
		}
		assert craigInterpolPos == interpolants.length;
		return result;
	}
	
	private AlternatingAutomaton<CodeBlock,IPredicate> computeAlternatingAutomaton(DataflowDAG<TraceCodeBlock> dag){
		AlternatingAutomaton<CodeBlock, IPredicate> alternatingAutomaton = new  AlternatingAutomaton<CodeBlock, IPredicate>(m_Abstraction.getAlphabet(), m_Abstraction.getStateFactory());
		IPredicate initialState = mPredicateUnifier.getFalsePredicate();
		IPredicate finalState = mPredicateUnifier.getTruePredicate();
		alternatingAutomaton.addState(initialState);
		alternatingAutomaton.setStateFinal(initialState);
		alternatingAutomaton.addState(finalState);
		alternatingAutomaton.addAcceptingConjunction(alternatingAutomaton.generateDisjunction(new IPredicate[]{finalState}, new IPredicate[0]));
		//build the automaton according to the structure of the dag
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
			}
			if(currentDag.getOutgoingNodes().isEmpty()){
				alternatingAutomaton.addTransition(
					currentDag.getNodeLabel().getBlock(),
					currentDag.getNodeLabel().getInterpolant(),
					alternatingAutomaton.generateDisjunction(new IPredicate[]{finalState}, new IPredicate[0])
				);
			}
		}
		//add transitions according to hoare triples
		for(CodeBlock letter : alternatingAutomaton.getAlphabet()){
			for(IPredicate sourceState : alternatingAutomaton.getStates()){
				for(IPredicate targetState : alternatingAutomaton.getStates()){
					if(m_SmtManager.isInductive(sourceState, letter, targetState) == LBool.UNSAT){
						alternatingAutomaton.generateDisjunction(new IPredicate[]{targetState}, new IPredicate[0]);
					}
				}
			}
		}
		return alternatingAutomaton;
	}

	private void getTermsFromDAG(DataflowDAG<TraceCodeBlock> dag, ArrayList<Term> terms, 
			ArrayList<Integer> startsOfSubtrees, int currentSubtree) {
		//		ArrayList<Term>	terms = new ArrayList<>();
		//		for (DataflowDAG<CodeBlock> outNode : dag.getOutgoingNodes()) {
		for (int i = 0; i < dag.getOutgoingNodes().size(); i++) {
			DataflowDAG<TraceCodeBlock> outNode = dag.getOutgoingNodes().get(i);
			//			getTermsFromDAG(outNode, terms, startsOfSubtrees, currentSubtree + i, traceCheckerFMIR);
			getTermsFromDAG(outNode, terms, startsOfSubtrees, 
					i == 0 ? currentSubtree : terms.size());
		}
		//		terms.add(dag.getNodeLabel().getTransitionFormula().getFormula());
		//		terms.add(traceCheckerFMIR.getAnnotatedSSATerm(dag.getNodeLabel().getIndex()));
		terms.add(traceCheckerWAST.getSSATerm(dag.getNodeLabel().getIndex()));
		startsOfSubtrees.add(currentSubtree);
		//		return null;
	}

	//TODO: not nice: this is copied from BasicCegarLoop, only difference: use another TraceChecker
	@Override
	protected LBool isCounterexampleFeasible() {
		IPredicate truePredicate = m_SmtManager.newTruePredicate();
		IPredicate falsePredicate = m_SmtManager.newFalsePredicate();
		//		PredicateUnifier predicateUnifier = new PredicateUnifier(mServices, m_SmtManager, truePredicate, falsePredicate);
		switch (m_Interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			m_TraceChecker = new TraceCheckerWithAccessibleSSATerms(truePredicate, falsePredicate, new TreeMap<Integer, IPredicate>(),//different TraceChecker, here..
					NestedWord.nestedWord(m_Counterexample.getWord()), m_SmtManager, m_RootNode.getRootAnnot()
					.getModGlobVarManager(), m_AssertCodeBlocksIncrementally, m_Services);
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			m_TraceChecker = new TraceCheckerSpWp(truePredicate, falsePredicate, new TreeMap<Integer, IPredicate>(),
					NestedWord.nestedWord(m_Counterexample.getWord()), m_SmtManager, m_RootNode.getRootAnnot()
					.getModGlobVarManager(), m_AssertCodeBlocksIncrementally, UnsatCores.CONJUNCT_LEVEL, true, m_Services);
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		LBool feasibility = m_TraceChecker.isCorrect();
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(m_Counterexample.getWord());
			String indentation = "";
			indentation += "  ";
			for (int j = 0; j < counterexample.length(); j++) {
				String stmts = counterexample.getSymbol(j).getPrettyPrintedStatements();
				// System.out.println(indentation + stmts);
				// s_Logger.info(indentation + stmts);
				if (counterexample.isCallPosition(j)) {
					indentation += "    ";
				}
				if (counterexample.isReturnPosition(j)) {
					indentation = indentation.substring(0, indentation.length() - 4);
				}
			}
			m_TraceChecker.computeRcfgProgramExecution();
			// s_Logger.info("Trace with values");
			// s_Logger.info(m_TraceChecker.getRcfgProgramExecution());
			m_RcfgProgramExecution = m_TraceChecker.getRcfgProgramExecution();
		} else {
			//			AllIntegers allInt = new TraceChecker.AllIntegers(); //difference
			//			m_TraceChecker.computeInterpolants(allInt, predicateUnifier, m_Interpolation); //difference
		}

		//		m_CegarLoopBenchmark.addTraceCheckerData(m_TraceChecker.getTraceCheckerBenchmark()); //do this somewhere else TODO //difference
		// m_TraceCheckerBenchmark.aggregateBenchmarkData(m_TraceChecker.getTraceCheckerBenchmark());

		return feasibility;
	}

}
