package local.stalin.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.model.boogie.ast.AssumeStatement;

/**
 * Specifies properties of a state in a graph representation of a system.
 * These properties are
 * <ul>
 * <li> Name of a location m_LocationName </li>
 * <li> Name of a procedure m_ProcedureName </li>
 * <li> Violations to the correctness of the system, stored in a map
 *  m_Violations. If one of the AssumeStatements in the keySet can be executed
 *  in this state, the system is not correct. Every AssumeStatement is mapped
 *  to a corresponding TransitionFormula.
 * </li>
 * <li> Possible valuations of variables in this state m_StateFormulas</li>
 * </ul>
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

public class RCfgState extends StateFormula
                        implements IProgramState {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 72852101509650437L;
	
	Map<AssumeStatement,TransFormula> m_Violations;
	String m_FormulaString;
	List<Formula> m_FormulaList = new ArrayList<Formula>();
	Map<Formula,Formula> m_FormulaMapping = new HashMap<Formula,Formula>();

	public RCfgState(ProgramPoint programPoint) {
		super(programPoint, null, new HashSet<String>(), new HashSet<String>());
	}
	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "Violations", "FormulaString", "Formula", "Vars",
		"OldVars", "FormulaList", "FormulaMapping"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Violations")
			return m_Violations;
		else if (field == "FormulaString")
			return m_FormulaString;
		else if (field == "FormulaList")
			return m_FormulaList;
		else if (field == "FormulaMapping")
			return m_FormulaMapping;
		else 
			return super.getFieldValue(field);
	}

	public void setViolations(Map<AssumeStatement, TransFormula> violations) {
		m_Violations = violations;
	}

	
	
	public void addState(IProgramState state, Theory theory) {
		super.m_Vars.addAll(state.getVars());
		super.m_OldVars.addAll(state.getOldVars());
		if (super.m_Formula == null) {
			super.m_Formula = state.getFormula();
		}
		else {
			m_Formula = theory.or(m_Formula,state.getFormula());
			m_FormulaList.add(state.getFormula());
		}
		m_FormulaString = m_Formula.toString();
	}
	

	@Override
	public Formula getFormula() {
		return m_Formula;
	}

//	@Override
//	public Map<String, ApplicationTerm> getOldVars() {
//		// TODO Auto-generated method stub
//		return null;
//	}

//	@Override
//	public Map<String, ApplicationTerm> getVars() {
//		// TODO Auto-generated method stub
//		return null;
//	}

	@Override
	public boolean isFalse() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isTrue() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<IProgramState> getConjunction() {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * @return the m_FormulaMapping
	 */
	public Map<Formula, Formula> getFormulaMapping() {
		return m_FormulaMapping;
	}
	
	

	/* (non-Javadoc)
	 * @see local.stalin.model.AbstractAnnotations#toString()
	 */
//	@Override
//	public String toString() {
//		return m_LocationName;
//	}

	
	
}
