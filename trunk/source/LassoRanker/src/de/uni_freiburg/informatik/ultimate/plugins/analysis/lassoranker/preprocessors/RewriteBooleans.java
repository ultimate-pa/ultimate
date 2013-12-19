package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AuxVarGenerator;


/**
 * Replaces booleans variables b with b_bool > 0 where b_bool is a new variable
 * 
 * @author Jan Leike
 */
public class RewriteBooleans extends TermTransformer implements PreProcessor {
	private static final String s_auxInfix = "_bool";
	
	private Script m_script;
	private AuxVarGenerator m_auxVarGenerator;
	
	/**
	 * Collects the translation of boolean variables and their real replacements
	 */
	private Map<String, TermVariable> m_Translation;
	
	public RewriteBooleans() {
		m_Translation = new HashMap<String, TermVariable>();
	}
	
	@Override
	public String getDescription() {
		return "Replaces a boolean variable b with b_bool > 0 "
				+ "where b_bool is a new variable";
	}
	
	/**
	 * Returns the auxiliary real variables corresponding to this variable name
	 * if one exists, otherwise return a fresh variable.
	 * 
	 * @param name a variable name
	 * @return the real auxiliary variable corresponding to this variable
	 */
	private TermVariable getAuxVar(String name) {
		if (m_Translation.containsKey(name)) {
			return m_Translation.get(name);
		}
		TermVariable auxVar = m_auxVarGenerator.newAuxVar(name + s_auxInfix,
				m_script.sort("Real"));
		m_Translation.put(name, auxVar);
		return auxVar;
	}
	
	@Override
	public Term process(Script script, Term term) {
		m_script = script;
		m_auxVarGenerator = new AuxVarGenerator(script, term);
		return transform(term);
	}
	
	/**
	 * @return the auxiliary variables generated during the process
	 */
	public Collection<TermVariable> getAuxVars() {
		return m_auxVarGenerator.getAuxVars();
	}
	
	@Override
	protected void convert(Term term) {
		assert(m_script != null);
		if (term instanceof TermVariable &&
				term.getSort().getName().equals("Bool")) {
			TermVariable auxVar = getAuxVar(((TermVariable) term).getName());
			setResult(m_script.term(">", auxVar, m_script.decimal("0")));
			return;
		}
		super.convert(term);
	}
}