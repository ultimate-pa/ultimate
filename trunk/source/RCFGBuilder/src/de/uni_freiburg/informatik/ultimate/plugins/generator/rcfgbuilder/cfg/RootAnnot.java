/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.model.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBacktranslator;

/**
 * Stores information about about a program that is not represented by the
 * recursive control flow graph.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class RootAnnot extends AbstractAnnotations {
	/**
	 * The serial version UID. Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;

	private final BoogieDeclarations m_BoogieDeclarations;

	/**
	 * Maps a procedure name to the entry node of that procedure. The entry node
	 * of a procedure represents an auxiliary location that is reached after
	 * calling the procedure. Afterwards we assume that the global variables and
	 * corresponding and oldvars have the same values, we assume the requires
	 * clause and reach the initial node.
	 * 
	 */
	final Map<String, ProgramPoint> m_entryNode = new HashMap<String, ProgramPoint>();

	/**
	 * Maps a procedure name to the final node of that procedure. The final node
	 * of a procedure represents the location that is reached after executing
	 * the last statement of the procedure or after executing a return
	 * statement. At this node the ensures part of the specification is asserted
	 * (has to be checked to prove correctness of the procedure). A sequence of
	 * edges that assumes the ensures part of the specification leads to the
	 * exit node of the procedure.
	 * 
	 */
	final Map<String, ProgramPoint> m_finalNode = new HashMap<String, ProgramPoint>();

	/**
	 * Maps a procedure name to the the exit node of that procedure. The exit
	 * node of a procedure represents an auxiliary location that is reached
	 * after assuming the ensures part of the specification. This locNode is the
	 * source of ReturnEdges which lead to the callers of this procecure.
	 */
	final Map<String, ProgramPoint> m_exitNode = new HashMap<String, ProgramPoint>();

	/**
	 * Maps the pair of procedure name location name to the LocNode that
	 * represents this location.
	 */
	final Map<String, Map<String, ProgramPoint>> m_LocNodes = new HashMap<String, Map<String, ProgramPoint>>();

	/**
	 * Maps a procedure name to error locations generated for this procedure.
	 */
	final Map<String, Collection<ProgramPoint>> m_ErrorNodes = new HashMap<String, Collection<ProgramPoint>>();
	/**
	 * Maps a {@code LocNode}s to the while loop that it represents
	 */
	final HashMap<ProgramPoint, ILocation> m_LoopLocations = new HashMap<ProgramPoint, ILocation>();

	private final Boogie2SMT m_Boogie2SMT;
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	private final CodeBlockFactory m_CodeBlockFactory;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "locNodes", "loopEntry" };

	public RootAnnot(IUltimateServiceProvider services, BoogieDeclarations boogieDeclarations, Boogie2SMT m_Boogie2smt,
			RCFGBacktranslator backtranslator) {
		m_BoogieDeclarations = boogieDeclarations;
		m_Boogie2SMT = m_Boogie2smt;
		m_ModifiableGlobalVariableManager = new ModifiableGlobalVariableManager(m_BoogieDeclarations.getModifiedVars(),
				m_Boogie2smt);
		m_CodeBlockFactory = new CodeBlockFactory(services, m_Boogie2SMT, m_ModifiableGlobalVariableManager);
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
			throw new UnsupportedOperationException("Unknown field " + field);
	}

	public Map<String, Map<String, ProgramPoint>> getProgramPoints() {
		return m_LocNodes;
	}

	public int getNumberOfProgramPoints() {
		int result = 0;
		for (String proc : getProgramPoints().keySet()) {
			result += getProgramPoints().get(proc).size();
		}
		return result;
	}

	public Map<String, ProgramPoint> getEntryNodes() {
		return m_entryNode;
	}

	public Map<String, ProgramPoint> getExitNodes() {
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

	public CodeBlockFactory getCodeBlockFactory() {
		return m_CodeBlockFactory;
	}

	public Set<ProgramPoint> getPotentialCycleProgramPoints() {
		final Set<ProgramPoint> relevantLocs = m_LocNodes.entrySet().stream()
				.flatMap(a -> a.getValue().entrySet().stream()).map(a -> a.getValue())
				.filter(a -> a.getOutgoingEdges().stream().anyMatch(b -> {
					final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(b);
					return loa != null && loa.getLoopEntryType() == LoopEntryType.GOTO;
				})).collect(Collectors.toSet());
		return relevantLocs;
	}

}
