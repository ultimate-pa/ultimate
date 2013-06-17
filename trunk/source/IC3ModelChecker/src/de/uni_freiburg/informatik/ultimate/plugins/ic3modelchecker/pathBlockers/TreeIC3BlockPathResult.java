package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.pathBlockers;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulasAndLevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.UnwindingNode;

public class TreeIC3BlockPathResult {
	private List<UnwindingNode> counterexample;
	// either counterexample or trace and edgeFormulasAndLvl are returned
	private ArrayList<Set<Clause>> trace;
	private FormulasAndLevelAnnotations edgeFormulasAndLvl;
	
	public TreeIC3BlockPathResult(List<UnwindingNode> counterexample, ArrayList<Set<Clause>> trace,
								  FormulasAndLevelAnnotations edgeFormulasAndLvl) {
		// exactly one part must be null:
		assert((counterexample != null) != (trace != null && edgeFormulasAndLvl != null));
		this.counterexample = counterexample;
		this.trace = trace;
		this.edgeFormulasAndLvl = edgeFormulasAndLvl;
	}
	
	public List<UnwindingNode> getCounterexample() {
		return this.counterexample;
	}
	
	public ArrayList<Set<Clause>> getTrace() {
		return this.trace;
	}
	
	public FormulasAndLevelAnnotations getEdgeFormulasAndLvl() {
		return this.edgeFormulasAndLvl;
	}
}
