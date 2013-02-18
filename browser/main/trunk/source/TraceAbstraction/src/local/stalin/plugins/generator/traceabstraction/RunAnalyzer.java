package local.stalin.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;

public class RunAnalyzer {
	Set<ProgramPoint> m_Cutpoints = new HashSet<ProgramPoint>();
	Set<Integer> m_CutpointPositions = new HashSet<Integer>(); 
	Map<ProgramPoint,Integer> m_Occurence = new HashMap<ProgramPoint,Integer>();
	
	public RunAnalyzer(NestedRun<TransAnnot, IProgramState> run) {
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

	Map<ProgramPoint,TransAnnot> m_NextStatement;
	
	private void analyze(NestedRun<TransAnnot, IProgramState> run) {
		m_NextStatement = new HashMap<ProgramPoint,TransAnnot>();
		NestedWord<TransAnnot> word = run.getNestedWord();
		ArrayList<IState<TransAnnot, IProgramState>> stateSequence = run.getStateSequence();
		for (int i=0; i<word.length(); i++) {
			ProgramPoint location = stateSequence.get(i).getContent().getProgramPoint();
			TransAnnot symbol = word.getSymbolAt(i);
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
			value = new Integer(1);
		}
		else {
			value = new Integer(++value);
		}
		m_Occurence.put(location,value);
	}
}
