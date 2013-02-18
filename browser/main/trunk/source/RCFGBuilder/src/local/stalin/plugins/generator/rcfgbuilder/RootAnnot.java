package local.stalin.plugins.generator.rcfgbuilder;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import local.stalin.logic.Theory;
import local.stalin.model.AbstractAnnotations;
import local.stalin.model.boogie.ast.ASTType;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.plugins.generator.rcfgbuilder.smt.BoogieVar2SmtVar;

/**
 * Stores information about about a program that is not represented by the
 * recursive control flow graph.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class RootAnnot extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	
	/**
	 * The list of all type, variable, constant, function and
	 * procedure.
	 */
	private final List<Declaration> m_Declarations;
	
	/**
	 * The list of all boogie axioms.
	 */
	private final List<Axiom> m_Axioms;
	
	/**
	 * The Theory, where we define all symbols, and axioms used while verifying
	 * this program.
	 */
	private Theory m_Theory;
	

	/**
	 * Maps procedure names to the Procedure objects that contain the
	 * specification of the procedure. 
	 */
	private final Map<String,Procedure> m_Procedures;
	
	/**
	 * Maps procedure names to the Procedure objects that contains the
	 * implementation of the procedure. 
	 */
	private final Map<String,Procedure> m_Implementations;
	
	/**
	 * Maps the pair of procedure name location name to the LocNode that
	 * represents this location.
	 */
	private final Map<String,Map<String,LocNode>> m_LocNodes;
	
	/**
	 * Maps a procedure name to the initial node of that procedure.
	 */
	private Map<String,LocNode> m_InitialNodes = 
								new HashMap<String,LocNode>();
	
	/**
	 * Maps procedure names to the set of global variables that can be modified
	 * by the procedure. These variables are represented as a map that assigns
	 * to variable names the type of the variable 
	 */
	private final Map<String,Map<String,ASTType>> m_ModifiedVars;
	
	
	/**
	 * Set of global variables defined in this program. The set of variables is
	 * represented as a map where the identifier of the variable is mapped to
	 * the type of the
	 * variable.  
	 */
	private final Map<String,ASTType> m_GlobalVars;
	
	/**
	 * TODO
	 */
	private BoogieVar2SmtVar m_BoogieVar2SmtVar;
	
	/**
	 * If true an InternalTransition represents a whole block, otherwise there
	 * is an InternalTransition for every single Statement.
	 */
	private final boolean m_MulipleStatementsPerTransition;

	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"declarations", "axioms", "theory",
		"procedures", "implementations", 
		"locNodes", "modifiedVars", "globalVars" , "BoogieVar2SmtVar" ,
		"MulipleStatementsPerTransition"
	};
	
	public RootAnnot(List<Declaration> declarations,
						   List<Axiom> axioms,
						   Map<String,Procedure> procedures,
						   Map<String,Procedure> implementations,
						   Map<String,Map<String,LocNode>> locNodes,
						   Map<String,LocNode> initialNode,
						   Map<String,Map<String,ASTType>> modifiedVars,
						   Map<String,ASTType> globalVars,
						   boolean mulipleStatementsPerTransition) {
		m_Declarations = declarations;
		m_Axioms = axioms;
		m_Procedures = procedures;
		m_Implementations = implementations;
		m_LocNodes = locNodes;
		m_InitialNodes = initialNode;
		m_ModifiedVars = modifiedVars;
		m_GlobalVars = globalVars;
		m_MulipleStatementsPerTransition = mulipleStatementsPerTransition;
		
	}
	
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
		else if (field == "theory")
			return m_Theory;
		else if (field == "procedures")
			return m_Procedures;
		else if (field == "implementations")
			return m_Implementations;
		else if (field == "locNodes")
			return m_LocNodes;
		else if (field == "modifiedVars")
			return m_ModifiedVars;
		else if (field == "globalVars")
			return m_GlobalVars;
		else if (field == "BoogieVar2SmtVar")
			return m_BoogieVar2SmtVar;
		else if (field == "MulipleStatementsPerTransition")
			return m_MulipleStatementsPerTransition;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}
	
	public void setTheory(Theory theory) {
		m_Theory = theory;
		m_BoogieVar2SmtVar = new BoogieVar2SmtVar(theory);
	}

	public List<Axiom> getAxioms() {
		return m_Axioms;
	}


	public Map<String, Procedure> getProcedures() {
		return m_Procedures;
	}

	public Map<String, Procedure> getImplementations() {
		return m_Implementations;
	}
	
	public Map<String,Map<String,LocNode>> getLocNodes() {
		return m_LocNodes;
	}
	
	public Map<String,LocNode> getInitialNodes() {
		return m_InitialNodes;
	}
	
	public Map<String, Map<String, ASTType>> getModifiedVars() {
		return m_ModifiedVars;
	}
	
	public Map<String, ASTType> getGlobalVars() {
		return m_GlobalVars;
	}

	public List<Declaration> getDeclarations() {
		return m_Declarations;
	}

	public Theory getTheory() {
		return m_Theory;
	}
	
	public BoogieVar2SmtVar getBoogieVar2SmtVar() {
		return m_BoogieVar2SmtVar;
	}
}
