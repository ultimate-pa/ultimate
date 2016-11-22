/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType.Type;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessModelToAutomatonTransformer;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private BoogieIcfgContainer mRcfgRootNode;
	private BoogieIcfgContainer mBlockEncodedRcfgRootNode;
	private IElement mRootOfNewModel;
	private WitnessNode mWitnessNode;
	private boolean mLastModel;
	private final IToolchainStorage mStorage;
	private ModelType mCurrentGraphType;

	public TraceAbstractionObserver(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastModel = false;
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof BoogieIcfgContainer) {
			if (isOriginalRcfg(mCurrentGraphType)) {
				if (mRcfgRootNode == null) {
					mRcfgRootNode = (BoogieIcfgContainer) root;
				} else {
					throw new UnsupportedOperationException("two RCFG models from same source");
				}
			}
			if (isBlockEncodingRcfg(mCurrentGraphType)) {
				if (mBlockEncodedRcfgRootNode == null) {
					mBlockEncodedRcfgRootNode = (BoogieIcfgContainer) root;
				} else {
					throw new UnsupportedOperationException("two RCFG models from same source");
				}
			}
		}
		if (root instanceof WitnessNode && mCurrentGraphType.getType() == Type.VIOLATION_WITNESS) {
			if (mWitnessNode == null) {
				mWitnessNode = (WitnessNode) root;
			} else {
				throw new UnsupportedOperationException("two witness models");
			}
		}
		return false;
	}

	private static boolean isBlockEncodingRcfg(final ModelType currentGraphType) {
		return "de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding"
				.equals(currentGraphType.getCreator());
	}

	private static boolean isOriginalRcfg(final ModelType currentGraphType) {
		return "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder"
				.equals(currentGraphType.getCreator());
	}

	@Override
	public void finish() {
		if (mLastModel) {
			final BoogieIcfgContainer rcfgRootNode;
			if (mBlockEncodedRcfgRootNode != null) {
				rcfgRootNode = mBlockEncodedRcfgRootNode;
			} else {
				rcfgRootNode = mRcfgRootNode;
			}

			if (rcfgRootNode == null) {
				throw new UnsupportedOperationException("TraceAbstraction needs an RCFG");
			}
			INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton;
			if (mWitnessNode == null) {
				witnessAutomaton = null;
			} else {
				mLogger.warn(
						"Found a witness automaton. I will only consider traces that are accepted by the witness automaton");
				witnessAutomaton = (new WitnessModelToAutomatonTransformer(mWitnessNode, mServices)).getResult();
			}
			final TraceAbstractionStarter tas =
					new TraceAbstractionStarter(mServices, mStorage, rcfgRootNode, witnessAutomaton);
			mRootOfNewModel = tas.getRootOfNewModel();
		}
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return mRootOfNewModel;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		mCurrentGraphType = modelType;
		if (currentModelIndex == numberOfModels - 1) {
			mLastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
