package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Backtranslator;

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
	 * Maps a procedure name to the entry node of that procedure.
	 * The entry node of a procedure represents an auxiliary location that is
	 * reached after calling the procedure. Afterwards we assume that the
	 * global variables and corresponding and oldvars have the same values,
	 * we assume the requires clause and reach the initial node.
	 * 
	 */
	final Map<String,ProgramPoint> m_entryNode = 
								new HashMap<String,ProgramPoint>();
	
	/**
	 * Maps a procedure name to the final node of that procedure.
	 * The final node of a procedure represents the location that is reached
	 * after executing the last statement of the procedure or after executing
	 * a return statement. At this node the ensures part of the specification is
	 * asserted (has to be checked to prove correctness of the procedure).
	 * A sequence of edges that assumes the ensures part of the specification
	 * leads to the exit node of the procedure.
	 * 
	 */
	final Map<String,ProgramPoint> m_finalNode = 
								new HashMap<String,ProgramPoint>();

	

	
	/**
	 * Maps a procedure name to the the exit node of that procedure.
	 * The exit node of a procedure represents an auxiliary location that is
	 * reached after assuming the ensures part of the specification. This
	 * locNode is the source of ReturnEdges which lead to the callers of this
	 * procecure.
	 */
	final Map<String,ProgramPoint> m_exitNode = 
								new HashMap<String,ProgramPoint>();
	
	
	/**
	 * Maps the pair of procedure name location name to the LocNode that
	 * represents this location.
	 */
	final Map<String,Map<String,ProgramPoint>> m_LocNodes =
								new HashMap<String,Map<String,ProgramPoint>>();
	
	/**
	 * Maps a procedure name to the requires clauses of the procedure
	 */
	final Map<String,List<RequiresSpecification>> m_Requires = 
								new HashMap<String,List<RequiresSpecification>>();

	/**
	 * Maps a procedure name to the requires clauses of the procedure which are
	 * not free. (A requires clause is not free if we have to proof that it
	 * holds.)
	 */
	final Map<String,List<RequiresSpecification>> m_RequiresNonFree = 
								new HashMap<String,List<RequiresSpecification>>();

	/**
	 * Maps a procedure name to the ensures clauses of the procedure
	 */
	final Map<String,List<EnsuresSpecification>> m_Ensures = 
								new HashMap<String,List<EnsuresSpecification>>();
	
	/**
	 * Maps a procedure name to the ensures clauses of the procedure which are
	 * not free. (A ensures clause is not free if we have to proof that it 
	 * holds.)
	 */
	final Map<String,List<EnsuresSpecification>> m_EnsuresNonFree = 
								new HashMap<String,List<EnsuresSpecification>>();
	
	/**
	 * Set of global variables defined in this program. The set of variables is
	 * represented as a map where the identifier of the variable is mapped to
	 * the type of the
	 * variable.  
	 */
	final Map<String,ASTType> m_GlobalVars = 
								new HashMap<String, ASTType>();

	/**
	 * Maps a procedure name to the set of global variables which may be
	 * modified by the procedure. The set of variables is represented as a map
	 * where the identifier of the variable is mapped to the type of the
	 * variable. 
	 */
	final Map<String,Map<String,ASTType>> m_ModifiedVars = 
								new HashMap<String,Map<String,ASTType>>();
	
	
	/**
	 * Maps a procedure name to the Procedure object that contains the
	 * specification of the procedure. 
	 */
	final Map<String,Procedure> m_Procedure = 
								new HashMap<String,Procedure>();
	
	/**
	 * Maps a procedure name to the Procedure object that contains the
	 * implementation of the procedure. 
	 */	
	final Map<String,Procedure> m_Implementation = 
								new HashMap<String,Procedure>();
	
	/**
	 * Maps a procedure name to error locations generated for this procedure.
	 */	
	final Map<String,Collection<ProgramPoint>> m_ErrorNodes = 
								new HashMap<String,Collection<ProgramPoint>>();
	/**
	 * Maps a {@code LocNode}s to the while loop that it represents
	 */
	final HashMap<ProgramPoint,ILocation> m_LoopLocations = new HashMap<ProgramPoint,ILocation>();
	

	/**
	 * TODO
	 */
	private Smt2Boogie m_BoogieVar2SmtVar;
	private Boogie2SMT m_Boogie2SMT;
	ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;





	private Backtranslator m_Backtranslator;




	
	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"procedures", "implementations", 
		"locNodes", "modifiedVars", "loopEntry", "globalVars" , 
		"BoogieVar2SmtVar"
	};
	
	public RootAnnot(
			Boogie2SMT m_Boogie2smt, Backtranslator backtranslator) {
		m_BoogieVar2SmtVar = m_Boogie2smt.getSmt2Boogie();
		m_Boogie2SMT = m_Boogie2smt;
		m_Backtranslator = backtranslator;
	}
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "procedures")
			return m_Procedure;
		else if (field == "implementations")
			return m_Implementation;
		else if (field == "locNodes")
			return m_LocNodes;
		else if (field == "loopEntry")
			return m_LoopLocations;
		else if (field == "modifiedVars")
			return m_ModifiedVars;
		else if (field == "BoogieVar2SmtVar")
			return m_BoogieVar2SmtVar;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}
	
	public Map<String, Procedure> getProcedures() {
		return m_Procedure;
	}

	public Map<String, Procedure> getImplementations() {
		return m_Implementation;
	}
	
	public Map<String,Map<String,ProgramPoint>> getProgramPoints() {
		return m_LocNodes;
	}
	
	public int getNumberOfProgramPoints() {
		int result = 0;
		for (String proc : getProgramPoints().keySet()) {
			result += getProgramPoints().get(proc).size();
		}
		return result;
	}
	
	public Map<String,ProgramPoint> getEntryNodes() {
		return m_entryNode;
	}
	
	public Map<String,ProgramPoint> getExitNodes() {
		return m_exitNode;
	}
	
	public Map<String, Collection<ProgramPoint>> getErrorNodes() {
		return m_ErrorNodes;
	}
	
	public ModifiableGlobalVariableManager getModGlobVarManager() {
		return m_ModifiableGlobalVariableManager;
	}
	
	public Map<String, ASTType> getGlobalVars() {
		return m_GlobalVars;
	}

	public Script getScript() {
		return m_Boogie2SMT.getScript();
	}
	
	public Smt2Boogie getBoogie2Smt() {
		return m_BoogieVar2SmtVar;
	}
	
	public Boogie2SMT getBoogie2SMT() {
		return m_Boogie2SMT;
	}

	public Map<ProgramPoint, ILocation> getLoopLocations() {
		return m_LoopLocations;
	}


	
	
}
