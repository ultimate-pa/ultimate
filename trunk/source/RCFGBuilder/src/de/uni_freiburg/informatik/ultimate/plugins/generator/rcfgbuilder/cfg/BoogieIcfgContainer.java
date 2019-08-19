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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;

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
	private static final boolean PREPEND_CLASSNAME_TO_IDENTIFIER = false;
	private static final String KEY = BoogieIcfgContainer.class.getName();

	private final BoogieDeclarations mBoogieDeclarations;
	private final Map<String, BoogieIcfgLocation> mEntryNodes;
	private final Map<String, BoogieIcfgLocation> mExitNode;
	private final Set<BoogieIcfgLocation> mLoopLocations;
	private final Map<String, Set<BoogieIcfgLocation>> mErrorNodes;
	private final Map<String, Map<DebugIdentifier, BoogieIcfgLocation>> mLocNodes;

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
	private final CodeBlockFactory mCodeBlockFactory;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final IPayload mPayload;
	private final Set<BoogieIcfgLocation> mInitialNodes;

	public BoogieIcfgContainer(final IUltimateServiceProvider services, final BoogieDeclarations boogieDeclarations,
			final Boogie2SMT mBoogie2smt, final ConcurrencyInformation concurInfo) {

		mEntryNodes = new HashMap<>();
		mExitNode = new HashMap<>();
		mFinalNode = new HashMap<>();
		mLocNodes = new HashMap<>();
		mErrorNodes = new HashMap<>();
		mLoopLocations = new HashSet<>();
		mInitialNodes = new HashSet<>();

		mBoogieDeclarations = boogieDeclarations;
		mBoogie2SMT = mBoogie2smt;
		final ManagedScript mgScript = mBoogie2smt.getManagedScript();
		final Set<String> procs = new HashSet<>();
		procs.addAll(boogieDeclarations.getProcImplementation().keySet());
		procs.addAll(boogieDeclarations.getProcSpecification().keySet());
		final SerialProvider serialprovider = new SerialProvider();
		mCfgSmtToolkit = new CfgSmtToolkit(
				new ModifiableGlobalsTable(
						mBoogie2smt.getBoogie2SmtSymbolTable().constructProc2ModifiableGlobalsMapping()),
				mgScript, mBoogie2smt.getBoogie2SmtSymbolTable(), procs,
				mBoogie2smt.getBoogie2SmtSymbolTable().getProc2InParams(),
				mBoogie2smt.getBoogie2SmtSymbolTable().getProc2OutParams(), new IcfgEdgeFactory(serialprovider),
				concurInfo, mBoogie2SMT.getSmtSymbols());
		mCodeBlockFactory = new CodeBlockFactory(services, mgScript, mCfgSmtToolkit,
				mBoogie2SMT.getBoogie2SmtSymbolTable(), serialprovider);
		mPayload = new Payload();
		mPayload.getAnnotations().put(KEY, this);
	}

	@Override
	@Visualizable
	public Map<String, Map<DebugIdentifier, BoogieIcfgLocation>> getProgramPoints() {
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

	public Boogie2SMT getBoogie2SMT() {
		return mBoogie2SMT;
	}

	@Override
	@Visualizable
	public Set<BoogieIcfgLocation> getLoopLocations() {
		return mLoopLocations;
	}

	public BoogieDeclarations getBoogieDeclarations() {
		return mBoogieDeclarations;
	}

	public CodeBlockFactory getCodeBlockFactory() {
		return mCodeBlockFactory;
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
		final String pathAndFilename = ILocation.getAnnotation(this).getFileName();
		return new File(pathAndFilename).getName();
	}

	/**
	 * @return Collection that contains all edges that are predecessor of the initial location of some procedure.
	 */
	public static Collection<IcfgEdge> extractStartEdges(final BoogieIcfgContainer root) {
		return IcfgUtils.extractStartEdges(root);
	}

	@Deprecated
	public RootNode constructRootNode() {
		final RootNode rootNode = new RootNode(ILocation.getAnnotation(this), this);
		for (final Entry<String, BoogieIcfgLocation> entry : getProcedureEntryNodes().entrySet()) {
			new RootEdge(rootNode, entry.getValue());
		}
		return rootNode;
	}

	@Override
	public String getIdentifier() {
		if (PREPEND_CLASSNAME_TO_IDENTIFIER) {
			return getClass().getSimpleName() + "_" + getFilename();
		}
		return getFilename();
	}

	@Override
	public Set<BoogieIcfgLocation> getInitialNodes() {
		return mInitialNodes;
	}

	@Override
	public Class<BoogieIcfgLocation> getLocationClass() {
		return BoogieIcfgLocation.class;
	}

	public static BoogieIcfgContainer getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (BoogieIcfgContainer) a);
	}

	@Override
	public String toString() {
		return graphStructureToString();
	}
}
