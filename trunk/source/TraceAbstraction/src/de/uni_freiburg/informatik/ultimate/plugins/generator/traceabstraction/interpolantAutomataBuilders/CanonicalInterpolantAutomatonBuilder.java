package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

/**
 * Constructs the canonical interpolant automaton. Boolean flags determine if we
 * also add selfloops in the initial and final state. I think this construction
 * is unsound if the precondition if not the "true" predicate.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class CanonicalInterpolantAutomatonBuilder extends CoverageAnalysis {

	private final NestedWordAutomaton<CodeBlock, IPredicate> m_IA;

	private final boolean m_SelfloopAtInitial = false;
	private final boolean m_SelfloopAtFinal = true;

	private final SmtManager m_SmtManager;

	private final Map<Integer, Set<IPredicate>> m_AlternativeCallPredecessors = new HashMap<Integer, Set<IPredicate>>();

	public CanonicalInterpolantAutomatonBuilder(TraceChecker traceChecker, List<ProgramPoint> programPointSequence,
			InCaReAlphabet<CodeBlock> alphabet, SmtManager smtManager, StateFactory<IPredicate> predicateFactory,
			Logger logger) {
		super(traceChecker, programPointSequence, logger);
		m_IA = new NestedWordAutomaton<CodeBlock, IPredicate>(alphabet.getInternalAlphabet(),
				alphabet.getCallAlphabet(), alphabet.getReturnAlphabet(), predicateFactory);
		m_SmtManager = smtManager;
	}

	protected void processCodeBlock(int i) {
		// interpolant after the CodeBlock
		IPredicate successorInterpolant = m_IPP.getInterpolant(i + 1);
		if (!m_IA.getStates().contains(successorInterpolant)) {
			assert (successorInterpolant != m_TraceChecker.getPostcondition());
			m_IA.addState(false, false, successorInterpolant);
		}
		addTransition(i, i, i + 1);
	}

	protected void processCoveringResult(int currentPosition, int previousOccurrence, LBool lbool) {
		if (lbool == LBool.UNSAT) {
			addTransition(currentPosition - 1, currentPosition - 1, previousOccurrence);
			addTransition(currentPosition, previousOccurrence, previousOccurrence + 1);
		}
	}

	protected void postprocess() {
		if (m_SelfloopAtInitial) {
			IPredicate precond = m_TraceChecker.getPrecondition();
			for (CodeBlock symbol : m_IA.getInternalAlphabet()) {
				m_IA.addInternalTransition(precond, symbol, precond);
			}
			for (CodeBlock symbol : m_IA.getCallAlphabet()) {
				m_IA.addCallTransition(precond, symbol, precond);
			}
			for (CodeBlock symbol : m_IA.getReturnAlphabet()) {
				m_IA.addReturnTransition(precond, precond, symbol, precond);
				for (Integer pos : m_AlternativeCallPredecessors.keySet()) {
					for (IPredicate hier : m_AlternativeCallPredecessors.get(pos)) {
						m_IA.addReturnTransition(precond, hier, symbol, precond);
					}
				}
			}
		}

		if (m_SelfloopAtFinal) {
			IPredicate postcond = m_TraceChecker.getPostcondition();
			for (CodeBlock symbol : m_IA.getInternalAlphabet()) {
				m_IA.addInternalTransition(postcond, symbol, postcond);
			}
			for (CodeBlock symbol : m_IA.getCallAlphabet()) {
				m_IA.addCallTransition(postcond, symbol, postcond);
			}
			for (CodeBlock symbol : m_IA.getReturnAlphabet()) {
				m_IA.addReturnTransition(postcond, postcond, symbol, postcond);
				for (Integer pos : m_AlternativeCallPredecessors.keySet()) {
					for (IPredicate hier : m_AlternativeCallPredecessors.get(pos)) {
						m_IA.addReturnTransition(postcond, hier, symbol, postcond);
					}
				}
			}
		}
	}

	protected void preprocess() {
		String interpolantAutomatonType = "Constructing canonical interpolant automaton";
		if (m_SelfloopAtInitial) {
			interpolantAutomatonType += ", with selfloop in true state";
		}
		if (m_SelfloopAtFinal) {
			interpolantAutomatonType += ", with selfloop in false state";
		}
		mLogger.info(interpolantAutomatonType);

		m_IA.addState(true, false, m_TraceChecker.getPrecondition());
		m_IA.addState(false, true, m_TraceChecker.getPostcondition());
	}

	public NestedWordAutomaton<CodeBlock, IPredicate> getInterpolantAutomaton() {
		return m_IA;
	}

	private void addTransition(int prePos, int symbolPos, int succPos) {
		IPredicate pred = m_IPP.getInterpolant(prePos);
		IPredicate succ = m_IPP.getInterpolant(succPos);
		CodeBlock symbol = m_NestedWord.getSymbol(symbolPos);
		if (m_NestedWord.isCallPosition(symbolPos)) {
			m_IA.addCallTransition(pred, symbol, succ);
			if (m_IPP.getInterpolant(prePos) != m_IPP.getInterpolant(symbolPos)) {
				addAlternativeCallPredecessor(symbolPos, m_IPP.getInterpolant(prePos));
			}
		} else if (m_NestedWord.isReturnPosition(symbolPos)) {
			int callPos = m_NestedWord.getCallPosition(symbolPos);
			IPredicate hier = m_IPP.getInterpolant(callPos);
			m_IA.addReturnTransition(pred, hier, symbol, succ);
			addAlternativeReturnTransitions(pred, callPos, symbol, succ);
		} else {
			m_IA.addInternalTransition(pred, symbol, succ);
		}
	}

	private void addAlternativeCallPredecessor(int symbolPos, IPredicate alternativeCallPredecessor) {
		Set<IPredicate> alts = m_AlternativeCallPredecessors.get(symbolPos);
		if (alts == null) {
			alts = new HashSet<IPredicate>();
			m_AlternativeCallPredecessors.put(symbolPos, alts);
		}
		alts.add(alternativeCallPredecessor);
	}

	private void addAlternativeReturnTransitions(IPredicate pred, int callPos, CodeBlock symbol, IPredicate succ) {
		if (m_AlternativeCallPredecessors.get(callPos) == null) {
			return;
		}
		for (IPredicate hier : m_AlternativeCallPredecessors.get(callPos)) {
			LBool isInductive = m_SmtManager.isInductiveReturn(pred, hier, (Return) symbol, succ);
			mLogger.debug("Trying to add alternative call Predecessor");
			if (isInductive == Script.LBool.UNSAT) {
				m_IA.addReturnTransition(pred, hier, symbol, succ);
				mLogger.debug("Added return from alternative call Pred");
			}
		}
	}

}