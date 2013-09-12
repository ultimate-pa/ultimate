package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;


/**
 * Given a counterexample in the abstraction, analyze if this counterexample
 * passed a loop.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class RunAnalyzer {
	Set<ProgramPoint> m_Cutpoints = new HashSet<ProgramPoint>();
	Set<Integer> m_CutpointPositions = new HashSet<Integer>(); 
	Map<ProgramPoint,Integer> m_Occurence = new HashMap<ProgramPoint,Integer>();
	
	public RunAnalyzer(IRun<CodeBlock, IPredicate> run) {
		analyze(run);
	}
	
	public Set<ProgramPoint> getCutpoints() {
		return m_Cutpoints;
	}
	
//	public Set<Integer> getCutpointPositions() {
//		return m_CutpointPositions;
//	}

	public Map<ProgramPoint, Integer> getOccurence() {
		return m_Occurence;
	}

	Map<ProgramPoint,CodeBlock> m_NextStatement;
	
	
	/*
	 * TODO: Unify version for concurrent and sequential programs
	 */
	private void analyze(IRun<CodeBlock, IPredicate> run) {
		m_NextStatement = new HashMap<ProgramPoint,CodeBlock>();
		Word<CodeBlock> word = run.getWord();
		ArrayList<IPredicate> stateSequence = null;
		if (run instanceof NestedRun) {
			NestedRun<CodeBlock, IPredicate> nestedRun = 
									(NestedRun<CodeBlock, IPredicate>) run;
			stateSequence = nestedRun.getStateSequence();
		}
		for (int i=0; i<word.length(); i++) {
			ProgramPoint location;
			if (run instanceof NestedRun) {
				location = ((ISLPredicate) stateSequence.get(i)).getProgramPoint();
			}
			else {
				location = null;
			}
			CodeBlock symbol = word.getSymbol(i);
			symbol.reportOccurenceInCounterexample();
			updateOccurence(location);
			if (m_NextStatement.containsKey(location)) {
				if (m_NextStatement.get(location) != symbol) {
					m_Cutpoints.add(location);
//					m_CutpointPositions.add(i);
				}

			}
			else {
				m_NextStatement.put(location, symbol);
			}
			
		}
	}
	
	private void updateOccurence(ProgramPoint location) {
		Integer value = m_Occurence.get(location);
		if (value == null) {
			value = Integer.valueOf(1);
		}
		else {
			value = Integer.valueOf(++value);
		}
		m_Occurence.put(location,value);
	}
}
