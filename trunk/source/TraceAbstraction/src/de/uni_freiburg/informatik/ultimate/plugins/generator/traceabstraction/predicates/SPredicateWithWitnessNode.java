package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class SPredicateWithWitnessNode extends SPredicate {

	/**
	 * 
	 */
	private static final long serialVersionUID = -3793267934783743767L;
	private final WitnessNode m_WitnessNode;
	private final Integer m_StutteringSteps;
	
	protected SPredicateWithWitnessNode(ProgramPoint programPoint,
			int serialNumber, String[] procedures, Term term,
			Set<BoogieVar> vars, Term closedFormula, WitnessNode witnessNode, Integer stutteringSteps) {
		super(programPoint, serialNumber, procedures, term, vars, closedFormula);
		m_WitnessNode = witnessNode;
		m_StutteringSteps = stutteringSteps;
	}
	
	@Override
	public String toString() {
		String result = super.m_SerialNumber + "#";
		result += "(";
//		if (m_ProgramPoint != null) {
			result += m_ProgramPoint.getPosition();
//		}
		result += ",";
		result += m_WitnessNode.getName();
		result += ",";
		result += m_StutteringSteps;
		result += ")";
		return result;
	}

}
