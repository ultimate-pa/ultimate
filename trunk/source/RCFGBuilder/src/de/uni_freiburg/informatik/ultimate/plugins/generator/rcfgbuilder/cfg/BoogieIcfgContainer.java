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

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBacktranslator;

/**
 * Stores references to all objects that represent an interprocedural control-flow graph (ICFG) that was directly
 * constructed from a Boogie program. The object is an {@link IAnnotations} but also an {@link IElement} whose
 * {@link IPayload} contains this object. (This is a workaround for getting information in the visualization).
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class BoogieIcfgContainer extends AbstractAnnotations implements IWalkable {
	/**
	 * The serial version UID. Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	private final BoogieDeclarations mBoogieDeclarations;
	
	/**
	 * Maps a procedure name to the entry node of that procedure. The entry node of a procedure represents an auxiliary
	 * location that is reached after calling the procedure. Afterwards we assume that the global variables and
	 * corresponding and oldvars have the same values, we assume the requires clause and reach the initial node.
	 * 
	 */
	final Map<String, BoogieIcfgLocation> mentryNode = new HashMap<String, BoogieIcfgLocation>();
	
	/**
	 * Maps a procedure name to the final node of that procedure. The final node of a procedure represents the location
	 * that is reached after executing the last statement of the procedure or after executing a return statement. At
	 * this node the ensures part of the specification is asserted (has to be checked to prove correctness of the
	 * procedure). A sequence of edges that assumes the ensures part of the specification leads to the exit node of the
	 * procedure.
	 * 
	 */
	final Map<String, BoogieIcfgLocation> mfinalNode = new HashMap<String, BoogieIcfgLocation>();
	
	/**
	 * Maps a procedure name to the the exit node of that procedure. The exit node of a procedure represents an
	 * auxiliary location that is reached after assuming the ensures part of the specification. This locNode is the
	 * source of ReturnEdges which lead to the callers of this procecure.
	 */
	final Map<String, BoogieIcfgLocation> mexitNode = new HashMap<String, BoogieIcfgLocation>();
	
	/**
	 * Maps the pair of procedure name location name to the LocNode that represents this location.
	 */
	final Map<String, Map<String, BoogieIcfgLocation>> mLocNodes =
			new HashMap<String, Map<String, BoogieIcfgLocation>>();
	
	/**
	 * Maps a procedure name to error locations generated for this procedure.
	 */
	final Map<String, Collection<BoogieIcfgLocation>> mErrorNodes =
			new HashMap<String, Collection<BoogieIcfgLocation>>();
	/**
	 * Maps a {@code LocNode}s to the while loop that it represents
	 */
	final HashMap<BoogieIcfgLocation, ILocation> mLoopLocations = new HashMap<BoogieIcfgLocation, ILocation>();
	
	private final Boogie2SMT mBoogie2SMT;
	private final ManagedScript mManagedScript;
	private final ModifiableGlobalVariableManager mModifiableGlobalVariableManager;
	private final CodeBlockFactory mCodeBlockFactory;
	
	private final CfgSmtToolkit mCfgSmtToolkit;
	
	private final IPayload mPayload;
	
	/**
	 * The published attributes. Update this and getFieldValue() if you add new attributes.
	 */
	private final static String[] s_AttribFields = { "locNodes", "loopEntry" };
	
	public BoogieIcfgContainer(final IUltimateServiceProvider services, final BoogieDeclarations boogieDeclarations,
			final Boogie2SMT mBoogie2smt, final RCFGBacktranslator backtranslator, final ILocation loc) {
		
		mBoogieDeclarations = boogieDeclarations;
		mBoogie2SMT = mBoogie2smt;
		mManagedScript = mBoogie2smt.getManagedScript();
		mModifiableGlobalVariableManager = new ModifiableGlobalVariableManager(mBoogieDeclarations.getModifiedVars(),
				mManagedScript, mBoogie2smt.getBoogie2SmtSymbolTable());
		mCfgSmtToolkit = new CfgSmtToolkit(mModifiableGlobalVariableManager, mManagedScript,
				mBoogie2smt.getBoogie2SmtSymbolTable());
		mCodeBlockFactory = new CodeBlockFactory(services, mManagedScript, mModifiableGlobalVariableManager,
				mBoogie2SMT.getBoogie2SmtSymbolTable());
		mPayload = new Payload(loc);
		mPayload.getAnnotations().put(Activator.PLUGIN_ID, this);
		
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
	
	public Map<String, Map<String, BoogieIcfgLocation>> getProgramPoints() {
		return mLocNodes;
	}
	
	public int getNumberOfProgramPoints() {
		int result = 0;
		for (final String proc : getProgramPoints().keySet()) {
			result += getProgramPoints().get(proc).size();
		}
		return result;
	}
	
	public Map<String, BoogieIcfgLocation> getEntryNodes() {
		return mentryNode;
	}
	
	public Map<String, BoogieIcfgLocation> getExitNodes() {
		return mexitNode;
	}
	
	public Map<String, Collection<BoogieIcfgLocation>> getErrorNodes() {
		return mErrorNodes;
	}
	
	public int getNumberOfErrorNodes() {
		int result = 0;
		for (final String proc : getErrorNodes().keySet()) {
			result += getErrorNodes().get(proc).size();
		}
		return result;
	}
	
	// public ModifiableGlobalVariableManager getModifiableGlobals() {
	// return mModifiableGlobalVariableManager;
	// }
	
	public Boogie2SMT getBoogie2SMT() {
		return mBoogie2SMT;
	}
	
	public Map<BoogieIcfgLocation, ILocation> getLoopLocations() {
		return mLoopLocations;
	}
	
	public BoogieDeclarations getBoogieDeclarations() {
		return mBoogieDeclarations;
	}
	
	public CodeBlockFactory getCodeBlockFactory() {
		return mCodeBlockFactory;
	}
	
	public Set<BoogieIcfgLocation> getPotentialCycleProgramPoints() {
		final Set<BoogieIcfgLocation> relevantLocs =
				mLocNodes.entrySet().stream().flatMap(a -> a.getValue().entrySet().stream()).map(a -> a.getValue())
						.filter(a -> a.getOutgoingEdges().stream().anyMatch(b -> {
							final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(b);
							return loa != null && loa.getLoopEntryType() == LoopEntryType.GOTO;
						})).collect(Collectors.toSet());
		return relevantLocs;
	}
	
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mCfgSmtToolkit;
	}
	
	@Override
	public IPayload getPayload() {
		return mPayload;
	}
	
	@Override
	public boolean hasPayload() {
		return true;
	}
	
	@Override
	public List<IWalkable> getSuccessors() {
		final List<IWalkable> result = new ArrayList<>();
		result.addAll(mentryNode.values());
		return result;
	}
	
	/**
	 * Returns the name of the file that is analyzed. The result is the name without the full path.
	 * 
	 */
	public String getFilename() {
		final String pathAndFilename = getPayload().getLocation().getFileName();
		final String pureFilename = new File(pathAndFilename).getName();
		return pureFilename;
	}
	
	/**
	 * @return Collection that contains all edges that are predecessor of the initial location of some procedure.
	 */
	public static Collection<IcfgEdge> extractStartEdges(final BoogieIcfgContainer root) {
		final List<IcfgEdge> startEdges = new ArrayList<>();
		for (final Entry<String, BoogieIcfgLocation> entry : root.getEntryNodes().entrySet()) {
			startEdges.addAll(entry.getValue().getOutgoingEdges());
		}
		return startEdges;
	}
	
	public RootNode constructRootNode() {
		final RootNode rootNode = new RootNode(getPayload().getLocation(), this);
		for (final Entry<String, BoogieIcfgLocation> entry : getEntryNodes().entrySet()) {
			new RootEdge(rootNode, entry.getValue());
		}
		return rootNode;
	}
	
}
