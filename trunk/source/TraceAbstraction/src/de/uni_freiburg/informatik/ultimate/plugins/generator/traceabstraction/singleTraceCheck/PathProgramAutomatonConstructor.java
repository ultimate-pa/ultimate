package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;


/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PathProgramAutomatonConstructor {
	
	/**
	 *  A mapping from positions of given path to states of the constructed automaton.
	 */
	private List<IPredicate> m_PositionsToStates;

	
	public List<IPredicate> getPositionsToStates() {
		return m_PositionsToStates;
	}
	
	/**
	 * Construct a path automaton (finite) from the given path.
	 */
	public INestedWordAutomaton<CodeBlock, IPredicate> constructAutomatonFromGivenPath(NestedWord<CodeBlock> path, IUltimateServiceProvider services, SmtManager smtManager,
			TAPreferences taPrefs) {
		// Set the alphabet
		Set<CodeBlock> internalAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>();
		for (int i = 0; i < path.length(); i++) {
			if (path.isInternalPosition(i)) {
				internalAlphabet.add(path.getSymbol(i));
			} else if (path.isCallPosition(i)) {
				callAlphabet.add(path.getSymbol(i));
			} else if (path.isReturnPosition(i)) {
				returnAlphabet.add(path.getSymbol(i));
			} else {
				throw new UnsupportedOperationException("Symbol at position " + i + " is neither internal, call, nor return symbol!");
			}
		}
		
		StateFactory<IPredicate> predicateFactory = new PredicateFactory(smtManager, taPrefs);
		// Create the automaton
		NestedWordAutomaton<CodeBlock, IPredicate> pathPA = new NestedWordAutomaton<CodeBlock, IPredicate>(services, internalAlphabet, callAlphabet, returnAlphabet, predicateFactory);
		
		m_PositionsToStates = new ArrayList<IPredicate>(path.length() + 1);
		// Add the initial state
		SPredicate sourceNode = smtManager.newTrueSLPredicate((ProgramPoint) path.getSymbol(0).getSource());
		pathPA.addState(true, false, sourceNode);
		m_PositionsToStates.add(0, sourceNode);
		// Add other states
		for (int i = 0; i < path.length(); i++) {
			SPredicate targetNode = smtManager.newTrueSLPredicate((ProgramPoint) path.getSymbol(i).getTarget());
			if (i + 1 == path.length()) {
				// this is the last (accepting) state (the error location)
				pathPA.addState(false, true, targetNode);
			} else {
				pathPA.addState(false, false, targetNode);
			}
			m_PositionsToStates.add(i+1, targetNode);
		}
		
		// Add the transitions
		for (int i = 0; i < path.length(); i++) {
			IPredicate pred = m_PositionsToStates.get(i);
			IPredicate succ = m_PositionsToStates.get(i+1);
			if (path.isInternalPosition(i)) {
				pathPA.addInternalTransition(pred, path.getSymbol(i), succ);
			} else if (path.isCallPosition(i)) {
				pathPA.addCallTransition(pred, path.getSymbol(i), succ);
			} else if (path.isReturnPosition(i)) {
				IPredicate hier = m_PositionsToStates.get(path.getCallPosition(i));
				pathPA.addReturnTransition(pred, hier, path.getSymbol(i), succ);
			}
		}
		return pathPA;
	}

}
