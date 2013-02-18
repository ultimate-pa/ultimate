package local.stalin.plugins.generator.rcfgbuilder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.model.AbstractAnnotations;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class RStateFormula extends AbstractAnnotations implements IProgramState {
	private static final long serialVersionUID = -2257982001512157622L;
	private final ProgramPoint m_ProgramPoint;
	private final Map<Formula,Formula> m_Formulas;
	private Formula m_Formula = Atom.TRUE;
	private final Set<String> m_CallerVars;
	private final Set<String> m_CallerOldVars;
	private final Set<String> m_CurrentVars;
	private final Set<String> m_CurrentOldVars;
	private Map<Integer,Map<Formula,Formula>> m_IterationFormulas =
		new HashMap<Integer,Map<Formula,Formula>>();
	private final Theory m_Theory;
	
	public RStateFormula(Theory theory,
			Map<Formula,Formula> formula,
			Set<String> callerVars,
			Set<String> callerOldVars,
			Set<String> currentVars,
			Set<String> currentOldVars) {
		m_Theory = theory;
		m_ProgramPoint = null;
		m_Formulas = formula;
		m_CallerVars = callerVars;
		m_CallerOldVars = callerOldVars;
		m_CurrentVars = currentVars;
		m_CurrentOldVars = currentOldVars;
		
		for (Formula callerF : m_Formulas.keySet()) {
			m_Formula = m_Theory.and(m_Formula, m_Formulas.get(callerF));
		}
	}
	
	public RStateFormula(Theory theory,
			ProgramPoint programPoint, 
			Map<Formula,Formula> formula,
			Set<String> callerVars,
			Set<String> callerOldVars,
			Set<String> currentVars,
			Set<String> currentOldVars) {
		m_Theory = theory;
		m_ProgramPoint = programPoint;
		m_Formulas = formula;
		m_CallerVars = callerVars;
		m_CallerOldVars = callerOldVars;
		m_CurrentVars = currentVars;
		m_CurrentOldVars = currentOldVars;
		
		for (Formula callerF : m_Formulas.keySet()) {
			m_Formula = m_Theory.and(m_Formula, m_Formulas.get(callerF));
		}

	}
	
	public RStateFormula(Theory theory, ProgramPoint programPoint) {
		m_Theory = theory;
		m_ProgramPoint = programPoint;
		m_Formulas = new HashMap<Formula,Formula>();
		m_CallerVars = new HashSet<String>(0);
		m_CallerOldVars = new HashSet<String>(0);
		m_CurrentVars = new HashSet<String>(0);
		m_CurrentOldVars = new HashSet<String>(0);
	}
	
	public RStateFormula(Theory theory) {
		m_Theory = theory;
		m_ProgramPoint = null;
		m_Formulas = new HashMap<Formula,Formula>();
		m_CallerVars = new HashSet<String>(0);
		m_CallerOldVars = new HashSet<String>(0);
		m_CurrentVars = new HashSet<String>(0);
		m_CurrentOldVars = new HashSet<String>(0);
	}
	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "Formulas", "CallerVars", "CallerOldVars",
		"CurrentVars", "CurrentOldVars", "IterationFormulas", "Formula"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "ProgramPoint")
			return m_ProgramPoint;
		else if (field == "Formulas")
			return m_Formulas;
		else if (field == "CallerVars")
			return m_CallerVars;
		else if (field == "CallerOldVars")
			return m_CallerOldVars;
		else if (field == "CurrentVars")
			return m_CurrentVars;
		else if (field == "CurrentOldVars")
			return m_CurrentOldVars;
		else if (field == "IterationFormulas")
			return m_IterationFormulas;
		else if (field == "Formula")
			return m_Formula;
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
	public Map<Formula,Formula> getFormulas() {
		return m_Formulas;
	}
	
	//TODO makeshift solution
	public Formula getFormula() {
		return m_Formula;
//		for (Formula callerF : m_Formulas.keySet()) {
//			result = m_Formulas.get(callerF);
//		}
//		if (m_Formulas.keySet().size() != 1) {
//			throw new UnsupportedOperationException();
//		}
//		return result;
	}
	
	public Set<String> getCallerVars() {
		return m_CallerVars;
	}

	public Set<String> getCallerOldVars() {
		return m_CallerOldVars;
	}

	public Set<String> getCurrentVars() {
		return m_CurrentVars;
	}

	public Set<String> getCurrentOldVars() {
		return m_CurrentOldVars;
	}
	
	public Map<Integer, Map<Formula, Formula>> getIterationFormulas() {
		return m_IterationFormulas;
	}

	public void createIterationFormulas(
			Map<Integer, Map<Formula, Formula>> iterationFormulas) {
		m_IterationFormulas = new HashMap<Integer, Map<Formula, Formula>>();
		for (Integer i : iterationFormulas.keySet()) {
			m_IterationFormulas.put(i,
					new HashMap<Formula, Formula>(iterationFormulas.get(i)));
		}
	}

	@Override
	public String toString() {
		if (m_ProgramPoint == null) {
			assert m_Formulas != null;
			return m_Formulas.toString();
		}
		else {
			return m_ProgramPoint.getLocation();
		}
	}



	// TODO use all fields for comparison
	public boolean equals(Object obj) {
		if (obj instanceof RStateFormula) {
			RStateFormula otherStateFormula = (RStateFormula) obj;
			return this.m_Formulas == otherStateFormula.m_Formulas;
		}
		else {
			return false;
		}
	}



	// TODO use all fields for comparison
	public int hashCode() {
		return m_Formulas.hashCode();
	}
	
	

	public static RStateFormula trueStateFormula(Theory theory) {
		return new RStateFormula(theory);
	}





	@Override
	public Set<IProgramState> getConjunction() {
		Set<IProgramState> conj = new HashSet<IProgramState>(1);
		conj.add(this);
		return conj;
	}
	

	public void add(Theory theory, IProgramState callerSf, IProgramState currentSf) {
		Formula thisCurrent = getFormulas().get(callerSf.getFormula());
		if (thisCurrent == null) {
			this.m_Formulas.put(callerSf.getFormula(), currentSf.getFormula());
		}
		else {
			Formula newCaller = theory.and(thisCurrent, currentSf.getFormula());
			this.m_Formulas.put(callerSf.getFormula(),newCaller);
		}
		this.m_CallerVars.addAll(callerSf.getVars());
		this.m_CallerOldVars.addAll(callerSf.getOldVars());
		this.m_CurrentVars.addAll(currentSf.getVars());
		this.m_CurrentOldVars.addAll(currentSf.getOldVars());
		
		this.m_Formula = theory.and(m_Formula, currentSf.getFormula());
	}


	public RStateFormula and(Theory theory, RStateFormula sf) {
		
		Map<Formula,Formula> newFormulas = new HashMap<Formula,Formula>();
		newFormulas.putAll(getFormulas());
		Map<Formula, Formula> sfFormulas = sf.getFormulas();
		for (Formula sfCaller : sfFormulas.keySet()) {
			Formula sfCurrent = sfFormulas.get(sfCaller);
			Formula newCurrent = newFormulas.get(sfCaller);
			if (newCurrent == null) {
				newFormulas.put(sfCaller, sfCurrent);
			}
			else {
				newFormulas.put(sfCaller, theory.and(newCurrent,sfCurrent));
			}			
		}
		
		Set<String> callerVars = new HashSet<String>();
		callerVars.addAll(this.getCallerVars());
		callerVars.addAll(sf.getCallerVars());
		Set<String> callerOldVars = new HashSet<String>();
		callerOldVars.addAll(this.getCallerOldVars());
		callerOldVars.addAll(sf.getCallerOldVars());
		
		Set<String> currentVars = new HashSet<String>();
		currentVars.addAll(this.getCurrentVars());
		currentVars.addAll(sf.getCurrentVars());
		Set<String> currentOldVars = new HashSet<String>();
		currentOldVars.addAll(this.getCurrentOldVars());
		currentOldVars.addAll(sf.getCurrentOldVars());
//		assert(newFormulas.keySet().size()==1);
		
		return new RStateFormula(m_Theory, this.getProgramPoint(),newFormulas,callerVars,callerOldVars,currentVars,currentOldVars);
	}

	//TODO makeshift solution
	@Override
	public boolean isFalse() {
		return false;
//		return (getFormula() == Atom.FALSE);
//		throw new UnsupportedOperationException("not yet implemented");
	}

	//TODO makeshift solution
	@Override
	public boolean isTrue() {
		return false;
//		return (getFormula() == Atom.TRUE);
//		throw new UnsupportedOperationException("not yet implemented");
	}

	//TODO makeshift solution
	@Override
	public Set<String> getOldVars() {
		return m_CurrentOldVars;
	}

	//TODO makeshift solution
	@Override
	public Set<String> getVars() {
		return m_CurrentVars;
	}

	//TODO makeshift solution
	@Override
	public boolean isUnknown() {
		//RState formula is never unknown  - if you need unknown use
		// State Formula
		return false;
	}


	
	 

}
