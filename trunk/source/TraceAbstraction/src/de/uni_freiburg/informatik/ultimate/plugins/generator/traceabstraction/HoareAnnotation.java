package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * Specifies properties of a state in a graph representation of a system.
 * These properties are
 * <ul>
 * <li> Name of a location m_LocationName </li>
 * <li> Name of a procedure m_ProcedureName </li>
 * <li> Possible valuations of variables in this state m_StateFormulas</li>
 * </ul>
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

public class HoareAnnotation extends SPredicate {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	/**
	 * 
	 */
	private static final long serialVersionUID = 72852101509650437L;
	
//	private final Script m_Script;
	private final SmtManager m_SmtManager;
	
	private final Map<Term,Term> m_Precondition2Invariant = 
												new HashMap<Term,Term>();
	private boolean m_IsUnknown = false;
	
	private boolean m_FormulaHasBeenComputed = false;

	public HoareAnnotation(ProgramPoint programPoint, int serialNumber, SmtManager smtManager) {
		super(programPoint, serialNumber, 
				new String[]{programPoint.getProcedure()}, smtManager.getScript().term("true"), 
				new HashSet<BoogieVar>(), null);
		m_SmtManager = smtManager;
	}
	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "StateIsUnknown" , "Formula", "Vars",
		"Precondition2InvariantMapping", 
		"Precondition2InvariantMappingAsStrings"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Precondition2InvariantMapping")
			return m_Precondition2Invariant;
		else if (field == "StateIsUnknown")
			return m_IsUnknown;
		else if (field == "Precondition2InvariantMappingAsStrings")
			return getPrecondition2InvariantMappingAsStrings();
		else 
			return super.getFieldValue(field);
	}

	
	public void addInvariant(IPredicate procPrecond, IPredicate locInvar) {
		if (m_FormulaHasBeenComputed) {
			throw new UnsupportedOperationException("Once Formula has been" +
					" computed it is not allowed to add new Formulas");
		}
		if (SmtManager.isDontCare(procPrecond) || SmtManager.isDontCare(locInvar)) {
			this.m_IsUnknown = true;
			return;
		}
		m_Vars.addAll(procPrecond.getVars());
		m_Vars.addAll(locInvar.getVars());
		Term procPrecondFormula = procPrecond.getFormula();
//		procPrecondFormula = (new SimplifyDDA(m_Script, s_Logger)).getSimplifiedTerm(procPrecondFormula);
		Term locInvarFormula = locInvar.getFormula();
		Term invarForPrecond = m_Precondition2Invariant.get(procPrecondFormula);
		if (invarForPrecond == null) {
			invarForPrecond = locInvarFormula;
		}
		else {
			invarForPrecond = Util.and(m_SmtManager.getScript(),invarForPrecond, locInvarFormula);
		}
//		invarForPrecond = (new SimplifyDDA(m_Script, s_Logger)).getSimplifiedTerm(invarForPrecond);
//		procPrecondFormula = (new SimplifyDDA(m_Script, s_Logger)).getSimplifiedTerm(procPrecondFormula);
		m_Precondition2Invariant.put(procPrecondFormula, invarForPrecond);
	}
	

	@Override
	public Term getFormula() {
		if (!m_FormulaHasBeenComputed) {
			computeFormula();
			m_FormulaHasBeenComputed = true;
		}
		return m_Formula;
	}
	
	private void computeFormula() {
		for (Term precond : getPrecondition2Invariant().keySet()) {
			Term precondTerm = Util.implies(m_SmtManager.getScript(),precond, 
					getPrecondition2Invariant().get(precond));
			s_Logger.debug("In "+ this + " holds " + getPrecondition2Invariant().get(precond) + " for precond " + precond);
			 m_Formula = Util.and(m_SmtManager.getScript(), m_Formula, precondTerm);	 
		}
		m_Formula = m_SmtManager.substituteOldVarsOfNonModifiableGlobals(
				getProgramPoint().getProcedure(), m_Vars, m_Formula);
		m_Formula = m_SmtManager.simplify(m_Formula);
		m_Formula = getPositiveNormalForm(m_Formula);
	}
	
	private Term getPositiveNormalForm(Term term) {
		Script script = m_SmtManager.getScript();
		Term result = (new AffineSubtermNormalizer(m_SmtManager.getScript())).transform(term);
		assert (Util.checkSat(script, script.term("distinct", term, result)) != LBool.SAT);
		return result;
	}
	

	/**
	 * @return the m_FormulaMapping
	 */
	public Map<Term, Term> getPrecondition2Invariant() {
		return m_Precondition2Invariant;
	}

	@Override
	public boolean isUnknown() {
		return m_IsUnknown;
	}
	
	public Map<String,String> getPrecondition2InvariantMappingAsStrings(){
		HashMap<String, String> result = new HashMap<String,String>();
		for (Entry<Term,Term> entry : m_Precondition2Invariant.entrySet()) {
			result.put(entry.getKey().toStringDirect(),entry.getValue().toStringDirect());
		}
		return result;
	}
	
	
	
}
