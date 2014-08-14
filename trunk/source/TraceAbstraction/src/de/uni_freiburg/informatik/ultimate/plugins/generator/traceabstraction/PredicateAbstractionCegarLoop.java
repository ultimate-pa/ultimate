package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

public class PredicateAbstractionCegarLoop extends BasicCegarLoop {

	public PredicateAbstractionCegarLoop(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks timingStatistics, TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			INTERPOLATION interpolation, boolean computeHoareAnnotation, IUltimateServiceProvider services) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, interpolation, computeHoareAnnotation, services);
		m_Haf = new HoareAnnotationFragments(mLogger);
	}

	@Override
	protected LBool isCounterexampleFeasible() {
		IPredicate precondition = super.m_SmtManager.newTruePredicate();
		IPredicate postcondition = super.m_SmtManager.newFalsePredicate();
		m_TraceChecker = new TraceChecker(precondition, postcondition, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(m_Counterexample.getWord()), m_SmtManager, m_RootNode.getRootAnnot()
						.getModGlobVarManager(), /*
												 * TODO: When Matthias
												 * introduced this parameter he
												 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
												 * Check if you want to set this
												 * to true.
												 */AssertCodeBlockOrder.NOT_INCREMENTALLY, mServices);

		LBool feasibility = m_TraceChecker.isCorrect();
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			Word<CodeBlock> counterexample = m_Counterexample.getWord();
			for (int j = 0; j < counterexample.length(); j++) {
				String stmts = counterexample.getSymbol(j).getPrettyPrintedStatements();
				mLogger.info(stmts);
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
		PredicateGuesser pg = new PredicateGuesser(m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager(),
				mLogger);
		IPredicate[] predicates = pg.extractPredicates((NestedWord<CodeBlock>) m_Counterexample.getWord());

		NestedWordAutomaton<CodeBlock, IPredicate> abstraction = (NestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction;
		NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
				abstraction.getInternalAlphabet(), abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(),
				abstraction.getStateFactory());
		IPredicate trueTerm = m_SmtManager.newTruePredicate();
		interpolantAutomaton.addState(true, false, trueTerm);
		IPredicate falseTerm = m_SmtManager.newFalsePredicate();
		interpolantAutomaton.addState(false, true, falseTerm);
		for (IPredicate sf : predicates) {
			interpolantAutomaton.addState(false, false, sf);
		}
		m_InterpolAutomaton = interpolantAutomaton;
	}

}
