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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.EpsilonNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType.Type;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.AutomataDefinitionInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessModelToAutomatonTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.EpsilonNestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final List<IIcfg<?>> mIcfgs;
	private IElement mRootOfNewModel;
	private WitnessNode mWitnessNode;
	private final List<AutomataTestFileAST> mAutomataTestFileAsts;
	private boolean mLastModel;
	private ModelType mCurrentGraphType;

	public TraceAbstractionObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastModel = false;
		mIcfgs = new ArrayList<>();
		mAutomataTestFileAsts = new ArrayList<>();
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof IIcfg<?>) {
			mIcfgs.add((IIcfg<?>) root);
		}
		if (root instanceof WitnessNode && mCurrentGraphType.getType() == Type.VIOLATION_WITNESS) {
			if (mWitnessNode == null) {
				mWitnessNode = (WitnessNode) root;
			} else {
				throw new UnsupportedOperationException("two witness models");
			}
		}
		if (root instanceof AutomataTestFileAST) {
			mAutomataTestFileAsts.add((AutomataTestFileAST) root);
		}
		return false;
	}

	@Override
	public void finish() {
		if (!mLastModel) {
			return;
		}

		if (mIcfgs.isEmpty()) {
			throw new IllegalArgumentException("No ICFG present, Trace Abstraction cannot run");
		}
		@SuppressWarnings("unchecked")
		final IIcfg<IcfgLocation> rcfgRootNode = (IIcfg<IcfgLocation>) mIcfgs.stream()
				.filter(a -> IcfgLocation.class.isAssignableFrom(a.getLocationClass())).reduce((a, b) -> b)
				.orElseThrow(UnsupportedOperationException::new);
		if (rcfgRootNode == null) {
			throw new UnsupportedOperationException("TraceAbstraction needs an RCFG");
		}
		mLogger.info("Analyzing ICFG " + rcfgRootNode.getIdentifier());
		INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton;
		if (mWitnessNode == null) {
			witnessAutomaton = null;
		} else {
			mLogger.warn(
					"Found a witness automaton. I will only consider traces that are accepted by the witness automaton");
			witnessAutomaton = new WitnessModelToAutomatonTransformer(mWitnessNode, mServices).getResult();
		}
		final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile =
				constructRawNestedWordAutomata(mAutomataTestFileAsts);
		final TraceAbstractionStarter tas = new TraceAbstractionStarter(mServices, rcfgRootNode, witnessAutomaton,
				rawFloydHoareAutomataFromFile);
		mRootOfNewModel = tas.getRootOfNewModel();
	}

	private List<INestedWordAutomaton<String, String>>
			constructRawNestedWordAutomata(final List<AutomataTestFileAST> automataTestFileAsts) {
		final List<INestedWordAutomaton<String, String>> result = new ArrayList<>();
		for (final AutomataTestFileAST automataTestFileAst : automataTestFileAsts) {
			final List<AutomatonAST> automataDefinitions =
					automataTestFileAst.getAutomataDefinitions().getListOfAutomataDefinitions();
			for (final AutomatonAST automatonDefinition : automataDefinitions) {
				if (automatonDefinition instanceof NestedwordAutomatonAST) {
					final NestedWordAutomaton<String, String> nwa = AutomataDefinitionInterpreter
							.constructNestedWordAutomaton((NestedwordAutomatonAST) automatonDefinition, mServices);
					result.add(nwa);
				} else if (automatonDefinition instanceof EpsilonNestedwordAutomatonAST) {
					final EpsilonNestedWordAutomaton<String, String, NestedWordAutomaton<String, String>> nwa =
							AutomataDefinitionInterpreter.constructEpsilonNestedWordAutomaton(
									(EpsilonNestedwordAutomatonAST) automatonDefinition, mServices);
					result.add(nwa);
				} else {
					throw new UnsupportedOperationException(
							"Reading " + automatonDefinition.getClass().getSimpleName() + " not yet supported");
				}
			}

		}
		return result;
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
