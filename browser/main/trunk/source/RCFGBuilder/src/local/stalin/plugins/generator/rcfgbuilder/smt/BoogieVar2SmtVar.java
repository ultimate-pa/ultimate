package local.stalin.plugins.generator.rcfgbuilder.smt;

import java.util.HashMap;
import java.util.Map;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.SMTLibBase;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.Theory;

/**
 * Maps from Boogie variables to the corresponding SMT variables.
 * The Boogie variables are represented as Strings (the identifier of the
 * variable). The SMT variables are represented by ApplicationTerms that
 * consist of one 0-ary function symbol (which represents a constant).
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BoogieVar2SmtVar {

	private final Theory m_Theory;
	public final Map<String,ApplicationTerm> m_Vars;
	public final Map<String,ApplicationTerm> m_OldVars;
	
	public BoogieVar2SmtVar(Theory theory) {
		m_Theory = theory;
		m_Vars = new HashMap<String,ApplicationTerm>();
		m_OldVars = new HashMap<String,ApplicationTerm>();
	}
	
	public ApplicationTerm getVariable(String varName, Sort sort) {
		ApplicationTerm constant = m_Vars.get(varName);
		if (constant == null) {
			constant = getConstantRepresentative(varName,sort);
			m_Vars.put(varName,constant);
		}
		else {
			if (constant.getSort() != sort) {
				throw new UnsupportedOperationException("Two variables" +
						" with different sort but same identifier not allowed");
			}
		}
		return constant;
	}
	
	
	public ApplicationTerm getOldVariable(String varName, Sort sort) {
		ApplicationTerm constant = m_OldVars.get(varName);
		if (constant == null) {
			constant = getConstantRepresentative(varName + "_OLD",sort);
			m_OldVars.put(varName,constant);
		}
		else {
			if (constant.getSort() != sort) {
				throw new UnsupportedOperationException("Two variables" +
						" with different sort but same identifier not allowed");
			}
		}
		return constant;
	}
	
	public ApplicationTerm getVariable(String varName) {
		ApplicationTerm constant = m_Vars.get(varName);
		if (constant == null) {
			throw new IllegalArgumentException("Variable does not exist");			
		}
		else {
			return constant;
		}
	}
	
	public ApplicationTerm getOldVariable(String varName) {
		ApplicationTerm constant = m_OldVars.get(varName);
		if (constant == null) {
			throw new IllegalArgumentException("Variable does not exist");			
		}
		else {
			return constant;
		}
	}
	
	public Theory getTheory() {
		return m_Theory;
	}

	/**
	 * Get constant that represents the Boogie variable with identifier varName 
	 */
	private ApplicationTerm getConstantRepresentative(String varName,Sort sort){
		String name = SMTLibBase.quoteId("v_"+varName);
		Sort[] emptySorts = {};
		FunctionSymbol func = m_Theory.getFunction(name, emptySorts); 
		if (func != null) {
			throw new AssertionError("Constant already exists");
		}
		func = m_Theory.createFunction(name, emptySorts, sort);
		Term[] emptyTerms = {};
		return m_Theory.term(func, emptyTerms);
	}
	
	
	
}
