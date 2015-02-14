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

import org.apache.log4j.Level;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AA_MergedUnion;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.BooleanExpression;
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
			IUltimateServiceProvider services) {
		super(name, rootNode, smtManager, traceAbstractionBenchmarks, taPrefs, errorLocs, services);
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
			AA_Determination<CodeBlock> determination = new AA_Determination<CodeBlock>(m_Services, alternatingAutomatonUnion, m_SmtManager, m_PredicateUnifier);
			m_InterpolAutomaton = determination.getResult();
			mLogger.info(m_InterpolAutomaton);
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
		FormulaWalker walker = new FormulaWalker(m_sfmv, m_SmtManager.getScript());

		Map<Term, IPredicate> withIndices2Predicate = new HashMap<Term, IPredicate>();

		int craigInterpolPos = 0;
		for (int resultPos = 0; resultPos < interpolants.length; resultPos++) {
			Term withIndices = interpolants[craigInterpolPos];
			craigInterpolPos++;
			result[resultPos] = withIndices2Predicate.get(withIndices);
			if (result[resultPos] == null) {
				m_sfmv.clearVarsAndProc();
				Term withoutIndices = walker.process(new FormulaUnLet().unlet(withIndices));
				Set<BoogieVar> vars = m_sfmv.getVars();
				String[] procs = m_sfmv.getProcedure().toArray(new String[0]);
				result[resultPos] = m_PredicateUnifier.getOrConstructPredicate(withoutIndices, vars, procs);
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
		alternatingAutomaton.setStateFinal(initialState);
		alternatingAutomaton.addAcceptingConjunction(alternatingAutomaton.generateDisjunction(new IPredicate[]{finalState}, new IPredicate[0]));
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
			BooleanExpression booleanExpression = alternatingAutomaton.generateDisjunction(new IPredicate[]{currentDag.getNodeLabel().getInterpolant()}, new IPredicate[0]);
			if(!targetStates.isEmpty()){
				for(IPredicate targetState : targetStates){
					alternatingAutomaton.addTransition(
						currentDag.getNodeLabel().getBlock(),
						targetState,
						booleanExpression
					);
				}
			}
			else{
				alternatingAutomaton.addTransition(
					currentDag.getNodeLabel().getBlock(),
					finalState,
					booleanExpression
				);
			}
		}
		//Add transitions according to hoare triples
		for(CodeBlock letter : alternatingAutomaton.getAlphabet()){
			for(IPredicate sourceState : alternatingAutomaton.getStates()){
				for(IPredicate targetState : alternatingAutomaton.getStates()){
					if(m_SmtManager.isInductive(sourceState, letter, targetState) == LBool.UNSAT){
						/*alternatingAutomaton.addTransition(
							letter,
							sourceState,
							alternatingAutomaton.generateDisjunction(new IPredicate[]{targetState}, new IPredicate[0])
						);*/
					}
				}
			}
		}
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
}
