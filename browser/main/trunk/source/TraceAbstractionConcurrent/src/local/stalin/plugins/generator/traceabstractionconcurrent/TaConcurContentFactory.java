package local.stalin.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import local.stalin.logic.Theory;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.LocNode;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.traceabstraction.CegarLoop;
import local.stalin.plugins.generator.traceabstraction.TAContentFactory;
import local.stalin.plugins.generator.traceabstraction.TAPreferences;

public class TaConcurContentFactory extends TAContentFactory {

	public TaConcurContentFactory(Map<String, Map<String, LocNode>> locNodes,
			CegarLoop cegarLoop, Theory theory,
			TAPreferences taPrefs,
			boolean hoareAnnotation,
			boolean interprocedural) {
		super(locNodes, cegarLoop, theory, taPrefs, hoareAnnotation, interprocedural);
		// TODO Auto-generated constructor stub
	}
	
	
	@Override
	public IProgramState getContentOnConcurrentProduct(IProgramState c1,
			IProgramState c2) {
		
		List<ProgramPoint> programPoints = new ArrayList<ProgramPoint>();
		ProdState result = new ProdState(programPoints);
		if (c1 instanceof ProdState) {
			ProdState ps1 = (ProdState) c1;
			programPoints.addAll(ps1.getProgramPoints());
		}
		else {
			programPoints.add(c1.getProgramPoint());
		}
		if (c2.getProgramPoint() == null) {
			assert (c2.getFormula() != null);
			result.and(m_Theory, (StateFormula) c2);
		}
		programPoints.add(c2.getProgramPoint()); 
		return result;
	}



	@Override
	public IProgramState getContentOnPetriNet2FiniteAutomaton(
			Collection<IProgramState> cList) {
		LinkedList<ProgramPoint> programPoints = new LinkedList<ProgramPoint>();
		for (IProgramState ps : cList) {
			programPoints.add(ps.getProgramPoint());
		}
		return new ProdState(programPoints);
	}
	
	

}
