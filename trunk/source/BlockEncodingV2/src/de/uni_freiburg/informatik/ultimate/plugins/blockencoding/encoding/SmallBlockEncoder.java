/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DuplicatedDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.DnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.XnfTransformer.AbortBeforeBlowup;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * {@link SmallBlockEncoder} tries to transform every internal transition to a DNF and if the resulting DNF has more
 * than one disjunct, removes the transition and adds for each disjunct a new transition.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class SmallBlockEncoder extends BaseBlockEncoder<IcfgLocation> {

	private static final int DNF_ONLY_IF_LESS_THAN = 35;

	private final IcfgEdgeBuilder mEdgeBuilder;

	private DnfTransformer mDnfTransformer;

	private NnfTransformer mNnfTransformer;

	private final Map<DebugIdentifier, Integer> mCloneCount;

	private Script mScript;

	/**
	 * Default constructor.
	 *
	 * @param edgeBuilder
	 * @param services
	 * @param backtranslator
	 * @param logger
	 */
	public SmallBlockEncoder(final IcfgEdgeBuilder edgeBuilder, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final ILogger logger) {
		super(logger, services, backtranslator);
		mEdgeBuilder = edgeBuilder;
		mCloneCount = new HashMap<>();

	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0;
	}

	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		final CfgSmtToolkit toolkit = icfg.getCfgSmtToolkit();
		mDnfTransformer = new DnfTransformer(toolkit.getManagedScript(), mServices, a -> a > DNF_ONLY_IF_LESS_THAN);
		mNnfTransformer = new NnfTransformer(toolkit.getManagedScript(), mServices, QuantifierHandling.KEEP);
		mScript = toolkit.getManagedScript().getScript();
		final IcfgLocationIterator<IcfgLocation> iter = new IcfgLocationIterator<>(icfg);
		final Set<IcfgEdge> toRemove = new HashSet<>();

		while (iter.hasNext()) {
			final IcfgLocation current = iter.next();
			processLocation(icfg, toRemove, current);
		}

		removeOldEdges(toRemove);
		return icfg;
	}

	private void processLocation(final BasicIcfg<IcfgLocation> icfg, final Set<IcfgEdge> toRemove,
			final IcfgLocation current) {
		final List<IcfgEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());

		for (final IcfgEdge edge : outEdges) {
			if (!(edge instanceof IIcfgInternalTransition<?>) || edge instanceof Summary) {
				// only internal transitions can be converted in DNF
				// summaries are not supported
				continue;
			}

			final UnmodifiableTransFormula tf = IcfgUtils.getTransformula(edge);
			Term term;
			try {
				term = mDnfTransformer.transform(tf.getFormula());
			} catch (final AbortBeforeBlowup exception) {
				if (edge.getTransformula().getAssignedVars().isEmpty()) {
					term = mNnfTransformer.transform(tf.getFormula());
				} else {
					continue;
				}

			}

			final Term[] disjuncts = SmtUtils.getDisjuncts(term);
			if (disjuncts.length > 1) {
				// top-level disjunction, remove this edge, replace by disjunctions
				if (!toRemove.add(edge)) {
					mLogger.warn("Unncessecary transformation");
					continue;
				}
				addEdgesFromDisjuncts(edge, disjuncts);
				continue;
			}

			final Term[] conjuncts = SmtUtils.getConjuncts(term);
			if (conjuncts.length == 1) {
				// its neither disjunction nor conjunction, so it should be a literal or relation
				// we keep this edge and move on
				continue;
			}

			// top-level conjunction; try to go down one level and extract all
			// conjuncts that are disjunctions by splitting it three ways:
			// - prefix without disjunctions
			// - the first disjunction
			// - the rest

			final List<Term> prefix = new ArrayList<>();
			Term[] disjunction = null;
			final List<Term> suffix = new ArrayList<>();
			for (int i = 0; i < conjuncts.length; ++i) {
				final Term[] subdisjuncts = SmtUtils.getDisjuncts(conjuncts[i]);
				if (subdisjuncts.length == 1) {
					prefix.add(subdisjuncts[0]);
				} else {
					disjunction = subdisjuncts;
					for (int j = i + 1; j < conjuncts.length; ++j) {
						suffix.add(conjuncts[j]);
					}
					break;
				}
			}

			if (disjunction == null) {
				// there was no disjunction, lets just keep this edge
				continue;
			}

			// we are going to remove this edge, check if we already did it
			if (!toRemove.add(edge)) {
				mLogger.warn("Unncessecary transformation");
				continue;
			}

			final IcfgLocation newSource;
			if (prefix.isEmpty()) {
				newSource = edge.getSource();
			} else {
				// we add a new edge between the old source and a new location and label it with the prefix
				newSource = createNewLocation(icfg, edge.getTarget());
				final Term prefixTerm = SmtUtils.and(mScript, prefix);
				final IcfgEdge newEdge =
						mEdgeBuilder.constructInternalTransition(edge, edge.getSource(), newSource, prefixTerm);
				rememberEdgeMapping(newEdge, edge);
			}

			final IcfgLocation newTarget;
			if (suffix.isEmpty()) {
				newTarget = edge.getTarget();
			} else {
				// we add a new edge between a new location and the old target and label it with the suffix
				newTarget = createNewLocation(icfg, edge.getTarget());
				final Term suffixTerm = SmtUtils.and(mScript, suffix);
				final IcfgEdge newEdge =
						mEdgeBuilder.constructInternalTransition(edge, newTarget, edge.getTarget(), suffixTerm);
				rememberEdgeMapping(newEdge, edge);
			}

			// finally, we add the disjunctions between newsource and newtarget
			for (final Term disjunct : disjunction) {
				final IcfgEdge newEdge = mEdgeBuilder.constructInternalTransition(edge, newSource, newTarget, disjunct);
				rememberEdgeMapping(newEdge, edge);
			}
		}
	}

	private void removeOldEdges(final Set<IcfgEdge> toRemove) throws AssertionError {
		final List<Pair<IcfgLocation, IcfgLocation>> locations = new ArrayList<>();
		toRemove.stream().forEach(a -> {
			locations.add(new Pair<>(a.getSource(), a.getTarget()));
			a.disconnectSource();
			a.disconnectTarget();
		});
		for (final Pair<IcfgLocation, IcfgLocation> location : locations) {
			final IcfgLocation source = location.getFirst();
			final IcfgLocation target = location.getSecond();
			if (target == null || source == null) {
				continue;
			}
			final IcfgLocationIterator<IcfgLocation> locIter = new IcfgLocationIterator<>(source);
			if (locIter.asStream().allMatch(a -> !a.equals(target))) {
				throw new AssertionError("Disconnected graph by removing connection between "
						+ source.getDebugIdentifier() + " and " + target.getDebugIdentifier());
			}
		}
		mRemovedEdges = toRemove.size();
	}

	private IcfgLocation createNewLocation(final BasicIcfg<IcfgLocation> icfg, final IcfgLocation oldLoc) {

		final DebugIdentifier oldIdentifier = oldLoc.getDebugIdentifier();
		final DebugIdentifier newIdentifier;
		Integer cloneCount = mCloneCount.get(oldIdentifier);
		if (cloneCount == null) {
			newIdentifier = new DuplicatedDebugIdentifier(oldIdentifier, 0);
			mCloneCount.put(oldIdentifier, 0);
		} else {
			cloneCount = cloneCount + 1;
			newIdentifier = new DuplicatedDebugIdentifier(oldIdentifier, cloneCount);
			mCloneCount.put(oldIdentifier, cloneCount);
		}
		final String proc = oldLoc.getProcedure();
		final IcfgLocation freshLoc = new IcfgLocation(newIdentifier, proc);

		// determine attributes of location
		final Set<IcfgLocation> errorLocs = icfg.getProcedureErrorNodes().get(proc);
		final boolean isError = errorLocs != null && errorLocs.contains(oldLoc);
		final boolean isProcEntry = oldLoc.equals(icfg.getProcedureEntryNodes().get(proc));
		final boolean isProcExit = oldLoc.equals(icfg.getProcedureExitNodes().get(proc));
		final boolean isLoopLocation = icfg.getLoopLocations().contains(oldLoc);
		final boolean isInitial = icfg.getInitialNodes().contains(oldLoc);

		// add fresh location to resultIcfg
		icfg.addLocation(freshLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);

		return freshLoc;
	}

	private void addEdgesFromDisjuncts(final IcfgEdge oldEdge, final Term[] disjuncts) {
		final IcfgLocation source = oldEdge.getSource();
		final IcfgLocation target = oldEdge.getTarget();
		for (final Term disjunct : disjuncts) {
			final IcfgEdge newEdge = mEdgeBuilder.constructInternalTransition(oldEdge, source, target, disjunct);
			rememberEdgeMapping(newEdge, oldEdge);
		}
	}

}
