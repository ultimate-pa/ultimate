package de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class SCNodeAnnotations extends AbstractAnnotations {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2362171497321338265L;

	HashMap<Term, TermVariable>	m_constants		= new HashMap<Term, TermVariable>();
	Term						m_interpolant	= null;// Atom.TRUE;
	Term						m_invariant		= null;// Atom.TRUE;
	CFGExplicitNode				m_primalNode	= null;	
	private final static String[] s_AttribFields = { 
		"constants", "interpolant", "invariant"
	};
	
	public SCNodeAnnotations(Term invariant) {
		m_interpolant = m_invariant = invariant; 
	}
	
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
	
	public void setInvariant(Term invariant){
		m_invariant = invariant;
	}
	public Term getInvariant(){
		return m_invariant;
	}
	
	public void setInterpolant(Term interpolant){
		m_interpolant = interpolant;
	}
	public Term getInterpolant(){
		return m_interpolant;
	}
	
	void setPrimalNode(CFGExplicitNode primalNode) {
		m_primalNode = primalNode;
	}
	
	CFGExplicitNode getPrimalNode() {
		return m_primalNode;
	}
	
	boolean isPrimalNode(CFGExplicitNode node) {
		return node == m_primalNode;
	}
}
