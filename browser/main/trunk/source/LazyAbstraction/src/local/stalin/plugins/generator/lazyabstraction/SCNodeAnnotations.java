package local.stalin.plugins.generator.lazyabstraction;

import java.util.HashMap;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.model.AbstractAnnotations;

public class SCNodeAnnotations extends AbstractAnnotations {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2362171497321338265L;

	HashMap<Term, TermVariable>	m_constants		= new HashMap<Term, TermVariable>();
	Formula						m_interpolant	= Atom.TRUE;
	Formula						m_invariant		= Atom.TRUE;
	
	private final static String[] s_AttribFields = { 
		"constants", "interpolant", "invariant"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "constants")
			return m_constants;
		else if (field == "interpolant")
			return m_interpolant;
		else if (field == "invariant")
			return m_invariant;
		else 
			throw new UnsupportedOperationException("Unknown field "+field);
	}
	
	public void setConstants(HashMap<Term, TermVariable> constants){
		m_constants = constants;
	}
	public HashMap<Term, TermVariable> getConstants(){
		return m_constants;
	}
	
	public void setInvariant(Formula invariant){
		m_invariant = invariant;
	}
	public Formula getInvariant(){
		return m_invariant;
	}
	
	public void setInterpolant(Formula interpolant){
		m_interpolant = interpolant;
	}
	public Formula getInterpolant(){
		return m_interpolant;
	}
}
