/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.woelfing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * An IcfgTransformer that accelerates loops.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Dennis Wölfing
 *
 */
public class LoopAccelerationIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final IIcfg<OUTLOC> mResultIcfg;
	private final ITransformulaTransformer mTransformer;

	private final Set<IcfgEdge> mLoopEntryTransitions;
	private final Map<INLOC, List<Backbone>> mBackbones;
	private final ManagedScript mScript;

	/**
	 * Constructs a LoopAccelerationIcfgTransformer.
	 *
	 * @param logger
	 *            A {@link ILogger} instance that is used for debug logging.
	 * @param originalIcfg
	 *            an input {@link IIcfg}.
	 * @param funLocFac
	 *            A location factory.
	 * @param backtranslationTracker
	 *            A backtranslation tracker.
	 * @param outLocationClass
	 *            The class object of the type of locations of the output {@link IIcfg}.
	 * @param newIcfgIdentifier
	 *            The identifier of the new {@link IIcfg}
	 * @param transformer
	 *            The transformer that should be applied to each transformula of each transition of the input
	 *            {@link IIcfg} to create a new {@link IIcfg}.
	 */
	public LoopAccelerationIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mTransformer = Objects.requireNonNull(transformer);

		mLoopEntryTransitions = new HashSet<>();
		mBackbones = new HashMap<>();
		mScript = origIcfg.getCfgSmtToolkit().getManagedScript();

		// perform transformation last
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
				new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, transformer, origIcfg, resultIcfg);
		mResultIcfg = transform(origIcfg, resultIcfg, lst);
		lst.finish();
	}

	/**
	 * Transforms the Icfg.
	 *
	 * @param lst
	 */
	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> origIcfg, final BasicIcfg<OUTLOC> resultIcfg,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		// Find all backbones for initial nodes.
		for (final INLOC initialNode : origIcfg.getInitialNodes()) {
			final List<Backbone> backbones = new ArrayList<>();
			for (final IcfgEdge edge : initialNode.getOutgoingEdges()) {
				backbones.addAll(findBackbones(edge));
			}
			mBackbones.put(initialNode, backbones);
		}

		// Find backbones for loop locations.
		for (final IcfgEdge entryTransition : mLoopEntryTransitions) {
			final List<Backbone> backbones = findBackbones(entryTransition);
			mBackbones.put((INLOC) entryTransition.getSource(), backbones);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Found the following backbones:");
			mLogger.debug(mBackbones);

			for (final INLOC location : mBackbones.keySet()) {
				mLogger.debug(location + ": " + getIteratedSymbolicMemoryForLoop(location));
			}
		}

		// Create a new Icfg.

		mTransformer.preprocessIcfg(origIcfg);

		final Set<INLOC> init = origIcfg.getInitialNodes();
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}

			final OUTLOC newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				final INLOC oldTarget = (INLOC) oldTransition.getTarget();
				open.add(oldTarget);
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				lst.createNewTransition(newSource, newTarget, oldTransition);
			}
		}
		return resultIcfg;
	}

	/**
	 * Finds backbones.
	 *
	 * @param entryTransition
	 *            The entry transition of the backbones.
	 * @return A list of backbones.
	 */
	private List<Backbone> findBackbones(final IcfgEdge entryTransition) {
		// TODO: This also gives backbones that end in assertions inside nested loops.

		final List<Backbone> incompleteBackbones = new ArrayList<>();
		final List<Backbone> completeBackbones = new ArrayList<>();
		incompleteBackbones.add(new Backbone(entryTransition));

		while (!incompleteBackbones.isEmpty()) {
			for (int i = incompleteBackbones.size() - 1; i >= 0; i--) {
				final Backbone backbone = incompleteBackbones.get(i);
				final INLOC lastLocation = (INLOC) backbone.getLastLocation();

				if (lastLocation != entryTransition.getSource() && backbone.endsInLoop()) {
					incompleteBackbones.remove(i);
					mLoopEntryTransitions.add(backbone.getLoopEntryTransition());
				} else if (lastLocation == entryTransition.getSource() || lastLocation.getOutgoingEdges().isEmpty()) {
					incompleteBackbones.remove(i);
					completeBackbones.add(backbone);
				}
			}

			final int backboneSize = incompleteBackbones.size();
			for (int i = 0; i < backboneSize; i++) {
				final Backbone backbone = incompleteBackbones.get(i);
				final INLOC location = (INLOC) backbone.getLastLocation();

				final List<IcfgEdge> outgoingEdges = location.getOutgoingEdges();
				for (int j = 0; j < outgoingEdges.size(); j++) {
					final IcfgEdge edge = outgoingEdges.get(j);
					if (j == outgoingEdges.size() - 1) {
						backbone.addTransition(edge);
					} else {
						final Backbone newBackbone = new Backbone(backbone);
						newBackbone.addTransition(edge);
						incompleteBackbones.add(newBackbone);
					}
				}
			}
		}

		return completeBackbones;
	}

	/**
	 * Calculates a TransFormula that holds after the given backbone was taken once.
	 * @param backbone
	 *            A Backbone.
	 * @return
	 *            A Transformula.
	 */
	private TransFormula getTransformulaForBackbone(final Backbone backbone) {
		Term term = mScript.getScript().term("true");

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();

		for (final IcfgEdge edge : backbone.getTransitions()) {
			final TransFormula tf = edge.getTransformula();

			for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
				if (!outVars.containsKey(entry.getKey())) {
					assert !inVars.containsKey(entry.getKey());
					inVars.put(entry.getKey(), entry.getValue());
				} else if (outVars.get(entry.getKey()) != entry.getValue()) {
					term = Util.and(mScript.getScript(), term,
							mScript.getScript().term("=", entry.getValue(), outVars.get(entry.getKey())));
				}
			}

			term = Util.and(mScript.getScript(), term, tf.getFormula());

			for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
				outVars.put(entry.getKey(), entry.getValue());
			}
		}

		final TransFormulaBuilder builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);
		builder.setFormula(term);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return builder.finishConstruction(mScript);
	}

	private IteratedSymbolicMemory getIteratedSymbolicMemoryForLoop(final INLOC loopEntry) {
		final List<Backbone> backbones = mBackbones.get(loopEntry);
		final List<SymbolicMemory> symbolicMemories = new ArrayList<>();

		for (final Backbone backbone : backbones) {
			final TransFormula tf = getTransformulaForBackbone(backbone);

			final SymbolicMemory symbolicMemory = new SymbolicMemory(tf);

			symbolicMemories.add(symbolicMemory);
		}

		return new IteratedSymbolicMemory(mScript, symbolicMemories);
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}
