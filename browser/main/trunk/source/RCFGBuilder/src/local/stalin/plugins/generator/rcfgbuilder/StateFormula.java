package local.stalin.plugins.generator.rcfgbuilder;

import java.util.HashSet;
import java.util.Set;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.model.AbstractAnnotations;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class StateFormula extends AbstractAnnotations implements IProgramState {
	private static final long serialVersionUID = -2257982001512157622L;
	protected final ProgramPoint m_ProgramPoint;
	protected Formula m_Formula;
	protected final Set<String> m_Vars;
	protected final Set<String> m_OldVars;
	
	/**
	 * If m_Unknown is true this formula represents a state in which no variable
	 * assignment is known. (opposed to Atom.True which means that every
	 * variable assignment is possible)  
	 */
	protected final boolean m_Unknown;
	
	public StateFormula(Formula formula,
			Set<String> vars,
			Set<String> oldVars) {
		m_ProgramPoint = null;
		m_Formula = formula;
		m_Vars = vars;
		m_OldVars = oldVars;
		if (formula == null) {
			m_Unknown = true;
		}
		else {
			m_Unknown = false;
		}
	}
	
	public StateFormula(ProgramPoint programPoint, 
			Formula formula,
			Set<String> vars,
			Set<String> oldVars) {
		m_ProgramPoint = programPoint;
		m_Formula = formula;
		m_Vars = vars;
		m_OldVars = oldVars;
		if (formula == null) {
			m_Unknown = true;
		}
		else {
			m_Unknown = false;
		}
	}
	
	public StateFormula(ProgramPoint programPoint) {
		m_ProgramPoint = programPoint;
		m_Formula = Atom.TRUE;
		m_Vars = new HashSet<String>(0);
		m_OldVars = new HashSet<String>(0);
		m_Unknown = false;
	}
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "Formula", "Vars", "OldVars"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "ProgramPoint")
			return m_ProgramPoint;
		else if (field == "Formula")
			return m_Formula;
		else if (field == "Vars")
			return m_Vars;
		else if (field == "OldVars")
			return m_OldVars;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}
	
	
	@Override
	public ProgramPoint getProgramPoint() {
		return m_ProgramPoint;
	}

	/**
	 * @return the m_Assertion
	 */
	public Formula getFormula() {
		return m_Formula;
	}

	public Set<String> getVars() {
		return m_Vars;
	}

	public Set<String> getOldVars() {
		return m_OldVars;
	}

	@Override
	public String toString() {
		if (m_ProgramPoint != null) {
			return m_ProgramPoint.getLocation();
		}
		else if (m_Unknown) {
			assert m_ProgramPoint == null;
			assert m_Formula == null;
			return "unknown";
		}
		else {
			assert m_Formula != null;
			return m_Formula.toString();
		}
	}



	// TODO use all fields for comparison
	public boolean equals(Object obj) {
		if (obj instanceof StateFormula) {
			StateFormula otherStateFormula = (StateFormula) obj;
			return this.m_ProgramPoint == otherStateFormula.m_ProgramPoint && 
			this.m_Formula == otherStateFormula.m_Formula;
		}
		else {
			return false;
		}
	}



	// TODO use all fields for comparison
	public int hashCode() {
		if (m_Unknown) {
			return super.hashCode();
		}
		else if (m_Formula == null) {
			return m_ProgramPoint.hashCode();
		}
		else if (m_ProgramPoint == null) {
			return m_Formula.hashCode();
		}
		else {
			return  3 * m_Formula.hashCode() + 5 * m_ProgramPoint.hashCode();
		}
	}
	
	

	public static StateFormula trueStateFormula() {
		return new StateFormula(Atom.TRUE, new HashSet<String>(0), new HashSet<String>(0));
	}



	@Override
	public boolean isFalse() {
		return m_Formula == Atom.FALSE;
	}



	@Override
	public boolean isTrue() {
		return m_Formula == Atom.TRUE;
	}

	public boolean isUnknown() {
		return m_Unknown;
	}


	@Override
	public Set<IProgramState> getConjunction() {
		Set<IProgramState> conj = new HashSet<IProgramState>(1);
		conj.add(this);
		return conj;
	}


	public StateFormula and(Theory theory, StateFormula sf) {
		boolean resultIsUnknownFormula = isUnknown() || sf.isUnknown();
		
		if (resultIsUnknownFormula) {
			return new StateFormula(this.getProgramPoint(), null, null, null);
		}
		else {
			Formula formula = theory.and(this.m_Formula,sf.getFormula());
			Set<String> vars = new HashSet<String>();
			vars.addAll(this.getVars());
			vars.addAll(sf.getVars());
			Set<String> oldVars = new HashSet<String>();
			oldVars.addAll(this.getOldVars());
			oldVars.addAll(sf.getOldVars());
			return	new StateFormula(this.getProgramPoint(), formula, vars, 
																	oldVars);
		}
		
	}


	
	 

}
