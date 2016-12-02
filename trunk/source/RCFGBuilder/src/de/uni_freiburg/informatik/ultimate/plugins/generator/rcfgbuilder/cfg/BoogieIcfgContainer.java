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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBacktranslator;

/**
 * Stores references to all objects that represent an interprocedural control-flow graph (ICFG) that was directly
 * constructed from a Boogie program. The object is an {@link IAnnotations} but also an {@link IElement} whose
 * {@link IPayload} contains this object. (This is a workaround for getting information in the visualization).
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BoogieIcfgContainer extends ModernAnnotations implements IIcfg<BoogieIcfgLocation> {
	/**
	 * The serial version UID. Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;

	private final BoogieDeclarations mBoogieDeclarations;
	private final Map<String, BoogieIcfgLocation> mEntryNodes;
	private final Map<String, BoogieIcfgLocation> mExitNode;
	private final Map<BoogieIcfgLocation, ILocation> mLoopLocations;
	private final Map<String, Set<BoogieIcfgLocation>> mErrorNodes;
	private final Map<String, Map<String, BoogieIcfgLocation>> mLocNodes;

	/**
	 * Maps a procedure name to the final node of that procedure. The final node of a procedure represents the location
	 * that is reached after executing the last statement of the procedure or after executing a return statement. At
	 * this node the ensures part of the specification is asserted (has to be checked to prove correctness of the
	 * procedure). A sequence of edges that assumes the ensures part of the specification leads to the exit node of the
	 * procedure.
	 *
	 * Note: This map is only used during construction!
	 *
	 */
	final Map<String, BoogieIcfgLocation> mFinalNode;

	private final Boogie2SMT mBoogie2SMT;
	private final ManagedScript mManagedScript;
	private final ModifiableGlobalsTable mModifiableGlobalVariableManager;
	private final CodeBlockFactory mCodeBlockFactory;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final IPayload mPayload;

	private Set<BoogieIcfgLocation> mPotentialCycleProgramPoints;

	public BoogieIcfgContainer(final IUltimateServiceProvider services, final BoogieDeclarations boogieDeclarations,
			final Boogie2SMT mBoogie2smt, final RCFGBacktranslator backtranslator, final ILocation loc) {

		mEntryNodes = new HashMap<>();
		mExitNode = new HashMap<>();
		mFinalNode = new HashMap<>();
		mLocNodes = new HashMap<>();
		mErrorNodes = new HashMap<>();
		mLoopLocations = new HashMap<>();

		mBoogieDeclarations = boogieDeclarations;
		mBoogie2SMT = mBoogie2smt;
		mManagedScript = mBoogie2smt.getManagedScript();
		mModifiableGlobalVariableManager = new ModifiableGlobalsTable(
				mBoogie2smt.getBoogie2SmtSymbolTable().constructProc2ModifiableGlobalsMapping());
		final Set<String> procs = new HashSet<>();
		procs.addAll(boogieDeclarations.getProcImplementation().keySet());
		procs.addAll(boogieDeclarations.getProcSpecification().keySet());
		mCfgSmtToolkit = new CfgSmtToolkit(mModifiableGlobalVariableManager, mManagedScript,
				mBoogie2smt.getBoogie2SmtSymbolTable(), mBoogie2SMT.getAxioms(), procs);
		mCodeBlockFactory =
				new CodeBlockFactory(services, mManagedScript, mCfgSmtToolkit, mBoogie2SMT.getBoogie2SmtSymbolTable());
		mPayload = new Payload(loc);
		mPayload.getAnnotations().put(Activator.PLUGIN_ID, this);
	}

	@Override
	@Visualizable
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

	@Override
	public Map<String, BoogieIcfgLocation> getProcedureEntryNodes() {
		return mEntryNodes;
	}

	@Override
	public Map<String, BoogieIcfgLocation> getProcedureExitNodes() {
		return mExitNode;
	}

	@Override
	public Map<String, Set<BoogieIcfgLocation>> getProcedureErrorNodes() {
		return mErrorNodes;
	}

	public int getNumberOfErrorNodes() {
		int result = 0;
		for (final String proc : getProcedureErrorNodes().keySet()) {
			result += getProcedureErrorNodes().get(proc).size();
		}
		return result;
	}

	// public ModifiableGlobalVariableManager getModifiableGlobals() {
	// return mModifiableGlobalVariableManager;
	// }

	public Boogie2SMT getBoogie2SMT() {
		return mBoogie2SMT;
	}

	/**
	 * Maps a {@code LocNode}s to the while loop that it represents
	 */
	@Visualizable
	public Map<BoogieIcfgLocation, ILocation> getLoopLocations() {
		return mLoopLocations;
	}

	public BoogieDeclarations getBoogieDeclarations() {
		return mBoogieDeclarations;
	}

	@Override
	public CodeBlockFactory getCodeBlockFactory() {
		return mCodeBlockFactory;
	}

	public Set<BoogieIcfgLocation> getPotentialCycleProgramPoints() {
		if (mPotentialCycleProgramPoints == null) {
			mPotentialCycleProgramPoints =
					getProgramPoints().entrySet().stream().flatMap(a -> a.getValue().entrySet().stream())
							.map(a -> a.getValue()).filter(a -> a.getOutgoingEdges().stream().anyMatch(b -> {
								final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(b);
								return loa != null && loa.getLoopEntryType() == LoopEntryType.GOTO;
							})).collect(Collectors.toSet());
		}
		return mPotentialCycleProgramPoints;
	}

	@Override
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
		for (final Entry<String, BoogieIcfgLocation> entry : root.getProcedureEntryNodes().entrySet()) {
			startEdges.addAll(entry.getValue().getOutgoingEdges());
		}
		return startEdges;
	}

	public RootNode constructRootNode() {
		final RootNode rootNode = new RootNode(getPayload().getLocation(), this);
		for (final Entry<String, BoogieIcfgLocation> entry : getProcedureEntryNodes().entrySet()) {
			new RootEdge(rootNode, entry.getValue());
		}
		return rootNode;
	}

	@Override
	public String getIdentifier() {
		return getClass().getSimpleName() + " " + getFilename();
	}
}
