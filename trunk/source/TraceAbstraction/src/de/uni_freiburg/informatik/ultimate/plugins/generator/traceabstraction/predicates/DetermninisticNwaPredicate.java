package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
@Deprecated
public class DetermninisticNwaPredicate extends BasicPredicate {


	private static final long serialVersionUID = -2257982001512157622L;
	private final Map<Term,Term> m_Formulas;
	private final Set<BoogieVar> m_CallerVars;
	private final Set<BoogieVar> m_CurrentVars;
	private final Script m_Theory;
	
	protected DetermninisticNwaPredicate(Script script, int serialNumber, Term term, String[] procedures,
			Set<BoogieVar> vars) {
		super(serialNumber, procedures, term, vars, null);
//		assert false : "Is this used any more?";
		m_Theory = script;
		m_Formulas = new HashMap<Term,Term>();
		m_CallerVars = new HashSet<BoogieVar>();
		m_CurrentVars = new HashSet<BoogieVar>();
	}
	
//	public DetermninisticNwaPredicate(Script theory,
//			Map<Term,Term> formula,
//			Set<BoogieVar> callerVars,
//			Set<BoogieVar> currentVars) {
//		m_Theory = theory;
//		m_ProgramPoint = null;
//		m_Formulas = formula;
//		m_CallerVars = callerVars;
//		m_CurrentVars = currentVars;
//		
//		for (Term callerF : m_Formulas.keySet()) {
//			m_Formula = Util.and(m_Theory, m_Formula, m_Formulas.get(callerF));
//		}
//		assert(m_Formula != null);
//	}
//	
//	public DetermninisticNwaPredicate(Script theory,
//			ProgramPoint programPoint, 
//			Map<Term,Term> formula,
//			Set<BoogieVar> callerVars,
//			Set<BoogieVar> callerOldVars,
//			Set<BoogieVar> currentVars,
//			Set<BoogieVar> currentOldVars) {
//		m_Theory = theory;
//		m_ProgramPoint = programPoint;
//		m_Formulas = formula;
//		m_CallerVars = callerVars;
//		m_CurrentVars = currentVars;
//		
//		for (Term callerF : m_Formulas.keySet()) {
//			m_Formula = Util.and(m_Theory, m_Formula, m_Formulas.get(callerF));
//		}
//		assert(m_Formula != null);
//	}
//	
//	public DetermninisticNwaPredicate(Script theory, ProgramPoint programPoint) {
//		m_Theory = theory;
//		m_ProgramPoint = programPoint;
//		m_Formulas = new HashMap<Term,Term>();
//		m_CallerVars = new HashSet<BoogieVar>(0);
//		m_CurrentVars = new HashSet<BoogieVar>(0);
//		assert(m_Formula != null);
//	}
	
//	public DetermninisticNwaPredicate(Script m_Script) {
//		super(null);
//		m_Theory = m_Script;
//		m_Formulas = new HashMap<Term,Term>();
//		m_CallerVars = new HashSet<BoogieVar>(0);
//		m_CurrentVars = new HashSet<BoogieVar>(0);
//		m_Formula = m_Script.term("true");
//		assert(m_Formula != null);
//	}
	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Procedures", "Formulas", "CallerVars",
		"CurrentVars", "Formula"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Formulas")
			return m_Formulas;
		else if (field == "CallerVars")
			return m_CallerVars;
		else if (field == "CurrentVars")
			return m_CurrentVars;
		else
			return super.getFieldValue(field);
	}
	
	
	/**
	 * @return the m_Assertion
	 */
	public Map<Term,Term> getFormulas() {
		return m_Formulas;
	}
	
	//TODO makeshift solution
	public Term getFormula() {
		return m_Formula;
//		for (Formula callerF : m_Formulas.keySet()) {
//			result = m_Formulas.get(callerF);
//		}
//		if (m_Formulas.keySet().size() != 1) {
//			throw new UnsupportedOperationException();
//		}
//		return result;
	}
	
	public Set<BoogieVar> getCallerVars() {
		return m_CallerVars;
	}


	public Set<BoogieVar> getCurrentVars() {
		return m_CurrentVars;
	}
	

//	public void createIterationFormulas(
//			Map<Integer, Map<Term, Term>> iterationFormulas) {
//		m_IterationFormulas = new HashMap<Integer, Map<Term, Term>>();
//		for (Integer i : iterationFormulas.keySet()) {
//			m_IterationFormulas.put(i,
//					new HashMap<Term, Term>(iterationFormulas.get(i)));
//		}
//	}



	// TODO use all fields for comparison
//	public boolean equals(Object obj) {
//		if (obj instanceof DetermninisticNwaPredicate) {
//			DetermninisticNwaPredicate otherStateFormula = (DetermninisticNwaPredicate) obj;
//			return this.m_Formulas == otherStateFormula.m_Formulas;
//		}
//		else {
//			return false;
//		}
//	}



	// TODO use all fields for comparison
//	public int hashCode() {
//		return m_Formulas.hashCode();
//	}
	
	

//	public static DetermninisticNwaPredicate trueStateFormula(Script theory) {
//		return new DetermninisticNwaPredicate(theory);
//	}






	public void add(Script theory, IPredicate callerSf, IPredicate currentSf) {
		Term thisCurrent = getFormulas().get(callerSf.getFormula());
		if (thisCurrent == null) {
			this.m_Formulas.put(callerSf.getFormula(), currentSf.getFormula());
		}
		else {
			Term newCaller = Util.and(m_Theory, thisCurrent, currentSf.getFormula());
			this.m_Formulas.put(callerSf.getFormula(),newCaller);
		}
		this.m_CallerVars.addAll(callerSf.getVars());
		this.m_CurrentVars.addAll(currentSf.getVars());
		
		this.m_Formula = Util.and(m_Theory, m_Formula, currentSf.getFormula());
	}


//	public DetermninisticNwaPredicate and(Script theory, DetermninisticNwaPredicate sf) {
//		
//		Map<Term,Term> newFormulas = new HashMap<Term,Term>();
//		newFormulas.putAll(getFormulas());
//		Map<Term, Term> sfFormulas = sf.getFormulas();
//		for (Term sfCaller : sfFormulas.keySet()) {
//			Term sfCurrent = sfFormulas.get(sfCaller);
//			Term newCurrent = newFormulas.get(sfCaller);
//			if (newCurrent == null) {
//				newFormulas.put(sfCaller, sfCurrent);
//			}
//			else {
//				newFormulas.put(sfCaller, Util.and(m_Theory, newCurrent, sfCurrent));
//			}			
//		}
//		
//		Set<BoogieVar> callerVars = new HashSet<BoogieVar>();
//		callerVars.addAll(this.getCallerVars());
//		callerVars.addAll(sf.getCallerVars());
//		Set<BoogieVar> callerOldVars = new HashSet<BoogieVar>();
//		
//		Set<BoogieVar> currentVars = new HashSet<BoogieVar>();
//		currentVars.addAll(this.getCurrentVars());
//		currentVars.addAll(sf.getCurrentVars());
//		Set<BoogieVar> currentOldVars = new HashSet<BoogieVar>();
//		
//		return new DetermninisticNwaPredicate(m_Theory, this.getProgramPoint(),newFormulas,callerVars,callerOldVars,currentVars,currentOldVars);
//	}


	//TODO makeshift solution
	@Override
	public Set<BoogieVar> getVars() {
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
