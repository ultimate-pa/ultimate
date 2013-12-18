package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

public class PredicateAbstractionCegarLoop extends BasicCegarLoop {

	public PredicateAbstractionCegarLoop(String name, RootNode rootNode,
			SmtManager smtManager,
			TimingStatistics timingStatistics,
			TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs) {
	
		super(name, rootNode, smtManager, timingStatistics, taPrefs, errorLocs);
		m_Haf = new HoareAnnotationFragments(rootNode.getRootAnnot(),super.m_SmtManager);
	}
	
	
	
	
	
	
	
	@Override
	protected LBool isCounterexampleFeasible() {
		IPredicate precondition = super.m_SmtManager.newTruePredicate();
		IPredicate postcondition = super.m_SmtManager.newFalsePredicate();
		m_TraceChecker = new TraceChecker(precondition, 
				postcondition, null, NestedWord.nestedWord(m_Counterexample.getWord()), m_SmtManager,
				m_RootNode.getRootAnnot().getModGlobVarManager());

		LBool feasibility = m_TraceChecker.isCorrect();
		if (feasibility != LBool.UNSAT) {
			s_Logger.info("Counterexample might be feasible");
			Word<CodeBlock> counterexample = m_Counterexample.getWord();
			for (int j=0; j < counterexample.length(); j++) {
				String stmts = counterexample.getSymbol(j).getPrettyPrintedStatements();
				s_Logger.info(stmts);
			}
			m_TraceChecker.computeRcfgProgramExecution();
			m_RcfgProgramExecution = m_TraceChecker.getRcfgProgramExecution();
		} else {
			m_TraceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
		}
		return feasibility;
	}

	
	@Override
	protected void constructInterpolantAutomaton() {
		PredicateGuesser pg = new PredicateGuesser(m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager());
		IPredicate[] predicates = pg.extractPredicates((NestedWord<CodeBlock>) m_Counterexample.getWord());

		NestedWordAutomaton<CodeBlock, IPredicate> abstraction = (NestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction;
		m_InterpolAutomaton = 
				new NestedWordAutomaton<CodeBlock, IPredicate>(
						abstraction.getInternalAlphabet(),
						abstraction.getCallAlphabet(),
						abstraction.getReturnAlphabet(),
						abstraction.getStateFactory());
		IPredicate trueTerm = m_SmtManager.newTruePredicate(); 
		m_InterpolAutomaton.addState(true, false, trueTerm);
		IPredicate falseTerm = m_SmtManager.newFalsePredicate();
		m_InterpolAutomaton.addState(false, true, falseTerm);
		for (IPredicate sf : predicates) {
			m_InterpolAutomaton.addState(false, false, sf);
		}
	}
	
	

}
