package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils;
/**
 * Constructs fresh TermVariables (i.e., TermVariables that have not been used
 * before).
 * @author Matthias Heizmann
 *
 */
public class VariableManager {
	private final MultiElementCounter<String> m_TvForBoogieVarCounter = 
			new MultiElementCounter<String>();
	private final Map<TermVariable, Term> m_TermVariable2Constant = 
			new HashMap<TermVariable, Term>();
	private final Script m_Script;
	
	VariableManager(Script script) {
		m_Script = script;
	}
	
	public TermVariable constructFreshTermVariable(BoogieVar bv) {
		final String name = bv.toString();
		final Integer newIndex = m_TvForBoogieVarCounter.increase(name);
		final Sort sort = bv.getTermVariable().getSort();
		TermVariable result = m_Script.variable(
				"v_" + name + "_" + newIndex, sort);
		return result;
	}
	
	public TermVariable constructFreshTermVariable(String name, Sort sort) {
		final Integer newIndex = m_TvForBoogieVarCounter.increase(name);
		TermVariable result = m_Script.variable(
				"v_" + name + "_" + newIndex, sort);
		return result;
	}
	
	public Term getCorrespondingConstant(TermVariable tv) {
		Term constant = m_TermVariable2Constant.get(tv);
		if (constant == null) {
			constant = SmtUtils.termVariable2constant(m_Script, tv);
			m_TermVariable2Constant.put(tv, constant);
		}
		return constant;
	}
	
//	/**
//	 * Declare new constant that has same name and same sort as tv.
//	 */
//	public Term constructConstant(TermVariable tv) {
//		String name = tv.getName();
//		Sort sort = tv.getSort();
//		m_Script.declareFun(name, new Sort[0], sort);
//		return m_Script.term(name);
//	}

	/**
	 * Construct a TermVariable whose name is given by the BoogieVar bv and
	 * and additional suffix. This TermVariable is not unified.
	 * If you use this method make sure that you do not call it twice for the
	 * same combination of bv and suffix.
	 */
	public TermVariable constructTermVariableWithSuffix(BoogieVar bv, String suffix) {
		final String name = bv.toString();
		final Integer newIndex = m_TvForBoogieVarCounter.increase(name);
		final Sort sort = bv.getTermVariable().getSort();
		TermVariable result = m_Script.variable(
				"v_" + name + "_" + newIndex, sort);
		return result;
	}
	
	

}
