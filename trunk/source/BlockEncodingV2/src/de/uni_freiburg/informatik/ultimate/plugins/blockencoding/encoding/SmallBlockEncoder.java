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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.DnfTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * {@link SmallBlockEncoder} tries to transform every internal transition to a DNF and if the resulting DNF has more
 * than one disjunct, removes the transition and adds for each disjunct a new transition.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class SmallBlockEncoder extends BaseBlockEncoder<IcfgLocation> {

	private final IcfgEdgeBuilder mEdgeBuilder;

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

	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0;
	}

	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		final CfgSmtToolkit toolkit = icfg.getCfgSmtToolkit();

		final IcfgLocationIterator<IcfgLocation> iter = new IcfgLocationIterator<>(icfg);
		final DnfTransformer dnfTransformer = new DnfTransformer(toolkit.getManagedScript(), mServices);

		final Set<IcfgEdge> toRemove = new HashSet<>();

		while (iter.hasNext()) {
			final IcfgLocation current = iter.next();
			final List<IcfgEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());

			for (final IcfgEdge edge : outEdges) {
				if (!(edge instanceof IIcfgInternalTransition<?>) || edge instanceof Summary) {
					// only internal transitions can be converted in DNF
					// summaries are not supported
					continue;
				}

				final UnmodifiableTransFormula tf = IcfgUtils.getTransformula(edge);
				final Term dnf = dnfTransformer.transform(tf.getFormula());
				final Term[] disjuncts = SmtUtils.getDisjuncts(dnf);
				if (disjuncts.length == 1) {
					// was already in dnf
					continue;
				}
				if (!toRemove.add(edge)) {
					mLogger.warn("Unncessecary transformation");
					continue;
				}
				addNewEdges(edge, disjuncts);
			}
		}

		toRemove.stream().forEach(a -> {
			a.disconnectSource();
			a.disconnectTarget();
		});
		mRemovedEdges = toRemove.size();

		return icfg;
	}

	private void addNewEdges(final IcfgEdge oldEdge, final Term[] disjuncts) {
		final IcfgLocation source = oldEdge.getSource();
		final IcfgLocation target = oldEdge.getTarget();
		for (final Term disjunct : disjuncts) {
			final IcfgEdge newEdge = mEdgeBuilder.constructInternalTransition(oldEdge, source, target, disjunct);
			rememberEdgeMapping(newEdge, oldEdge);
		}
	}
}
