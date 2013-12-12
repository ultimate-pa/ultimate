package de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;

public class CFGRootAnnotations extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	/**
	 * The list of all type, variable, constant, function and
	 * procedure declarations.
	 */
	private List<Declaration> m_Declarations = new ArrayList<Declaration>();
	/**
	 * The list of all boogie axioms.
	 */
	private List<Axiom> m_Axioms = new ArrayList<Axiom>();
	private Script m_Script;	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"declarations", "axioms", "script"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "declarations")
			return m_Declarations;
		else if (field == "axioms")
			return m_Axioms;
		else if (field == "script")
			return m_Script;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * Add a declaration.
	 * @param decl the declaration to add.
	 */
	public void addDeclaration(Declaration decl) {
		m_Declarations.add(decl);
	}

	/**
	 * Add an axiom.
	 * @param axiom the axiom to add.
	 */
	public void addAxiom(Axiom axiom) {
		m_Axioms.add(axiom);
	}
	
	public void setScript(Script script) {
		m_Script = script;
	}
	
	public List<Axiom> getAxioms() {
		return m_Axioms;
	}
	
	public List<Declaration> getDeclarations() {
		return m_Declarations;
	}
	
	public Script getScript() {
		return m_Script;
	}
	
}
