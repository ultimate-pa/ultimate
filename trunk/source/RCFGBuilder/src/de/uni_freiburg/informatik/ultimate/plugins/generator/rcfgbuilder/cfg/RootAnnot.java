package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
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
	
	private final BoogieDeclarations m_BoogieDeclarations;
	
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
//	private Smt2Boogie m_BoogieVar2SmtVar;
	private Boogie2SMT m_Boogie2SMT;
	ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;





	private Backtranslator m_Backtranslator;




	
	
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"locNodes", "loopEntry"
	};
	
	public RootAnnot(BoogieDeclarations boogieDeclarations,
			Boogie2SMT m_Boogie2smt, Backtranslator backtranslator) {
		m_BoogieDeclarations = boogieDeclarations;
		m_Boogie2SMT = m_Boogie2smt;
		m_Backtranslator = backtranslator;
	}
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "locNodes")
			return m_LocNodes;
		else if (field == "loopEntry")
			return m_LoopLocations;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
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
	
	public int getNumberOfErrorNodes() {
		int result = 0;
		for (String proc : getErrorNodes().keySet()) {
			result += getErrorNodes().get(proc).size();
		}
		return result;
	}
	
	public ModifiableGlobalVariableManager getModGlobVarManager() {
		return m_ModifiableGlobalVariableManager;
	}
	
	public Script getScript() {
		return m_Boogie2SMT.getScript();
	}
	

	public Boogie2SMT getBoogie2SMT() {
		return m_Boogie2SMT;
	}

	public Map<ProgramPoint, ILocation> getLoopLocations() {
		return m_LoopLocations;
	}

	public BoogieDeclarations getBoogieDeclarations() {
		return m_BoogieDeclarations;
	}

	

	
	
}
