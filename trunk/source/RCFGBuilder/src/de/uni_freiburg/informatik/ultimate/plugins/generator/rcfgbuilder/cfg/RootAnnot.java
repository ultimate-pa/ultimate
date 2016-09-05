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

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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

	private final BoogieDeclarations mBoogieDeclarations;

	/**
	 * Maps a procedure name to the entry node of that procedure. The entry node
	 * of a procedure represents an auxiliary location that is reached after
	 * calling the procedure. Afterwards we assume that the global variables and
	 * corresponding and oldvars have the same values, we assume the requires
	 * clause and reach the initial node.
	 * 
	 */
	final Map<String, ProgramPoint> mentryNode = new HashMap<String, ProgramPoint>();

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
	final Map<String, ProgramPoint> mfinalNode = new HashMap<String, ProgramPoint>();

	/**
	 * Maps a procedure name to the the exit node of that procedure. The exit
	 * node of a procedure represents an auxiliary location that is reached
	 * after assuming the ensures part of the specification. This locNode is the
	 * source of ReturnEdges which lead to the callers of this procecure.
	 */
	final Map<String, ProgramPoint> mexitNode = new HashMap<String, ProgramPoint>();

	/**
	 * Maps the pair of procedure name location name to the LocNode that
	 * represents this location.
	 */
	final Map<String, Map<String, ProgramPoint>> mLocNodes = new HashMap<String, Map<String, ProgramPoint>>();

	/**
	 * Maps a procedure name to error locations generated for this procedure.
	 */
	final Map<String, Collection<ProgramPoint>> mErrorNodes = new HashMap<String, Collection<ProgramPoint>>();
	/**
	 * Maps a {@code LocNode}s to the while loop that it represents
	 */
	final HashMap<ProgramPoint, ILocation> mLoopLocations = new HashMap<ProgramPoint, ILocation>();

	private final Boogie2SMT mBoogie2SMT;
	private final ManagedScript mManagedScript;
	private final ModifiableGlobalVariableManager mModifiableGlobalVariableManager;
	private final CodeBlockFactory mCodeBlockFactory;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "locNodes", "loopEntry" };

	public RootAnnot(final IUltimateServiceProvider services, final BoogieDeclarations boogieDeclarations, final Boogie2SMT mBoogie2smt,
			final RCFGBacktranslator backtranslator) {
		mBoogieDeclarations = boogieDeclarations;
		mBoogie2SMT = mBoogie2smt;
		mManagedScript = mBoogie2smt.getManagedScript();
		mModifiableGlobalVariableManager = new ModifiableGlobalVariableManager(mBoogieDeclarations.getModifiedVars(),
				mManagedScript, mBoogie2smt.getBoogie2SmtSymbolTable());
		mCodeBlockFactory = new CodeBlockFactory(services, mManagedScript, mModifiableGlobalVariableManager, mBoogie2SMT.getBoogie2SmtSymbolTable());
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(final String field) {
		if (field == "locNodes") {
			return mLocNodes;
		} else if (field == "loopEntry") {
			return mLoopLocations;
		} else {
			throw new UnsupportedOperationException("Unknown field " + field);
		}
	}

	public Map<String, Map<String, ProgramPoint>> getProgramPoints() {
		return mLocNodes;
	}

	public int getNumberOfProgramPoints() {
		int result = 0;
		for (final String proc : getProgramPoints().keySet()) {
			result += getProgramPoints().get(proc).size();
		}
		return result;
	}

	public Map<String, ProgramPoint> getEntryNodes() {
		return mentryNode;
	}

	public Map<String, ProgramPoint> getExitNodes() {
		return mexitNode;
	}

	public Map<String, Collection<ProgramPoint>> getErrorNodes() {
		return mErrorNodes;
	}

	public int getNumberOfErrorNodes() {
		int result = 0;
		for (final String proc : getErrorNodes().keySet()) {
			result += getErrorNodes().get(proc).size();
		}
		return result;
	}

	public ModifiableGlobalVariableManager getModGlobVarManager() {
		return mModifiableGlobalVariableManager;
	}

	public Script getScript() {
		return mBoogie2SMT.getScript();
	}
	
	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public Boogie2SMT getBoogie2SMT() {
		return mBoogie2SMT;
	}

	public Map<ProgramPoint, ILocation> getLoopLocations() {
		return mLoopLocations;
	}

	public BoogieDeclarations getBoogieDeclarations() {
		return mBoogieDeclarations;
	}

	public CodeBlockFactory getCodeBlockFactory() {
		return mCodeBlockFactory;
	}

	public Set<ProgramPoint> getPotentialCycleProgramPoints() {
		final Set<ProgramPoint> relevantLocs = mLocNodes.entrySet().stream()
				.flatMap(a -> a.getValue().entrySet().stream()).map(a -> a.getValue())
				.filter(a -> a.getOutgoingEdges().stream().anyMatch(b -> {
					final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(b);
					return loa != null && loa.getLoopEntryType() == LoopEntryType.GOTO;
				})).collect(Collectors.toSet());
		return relevantLocs;
	}

}
