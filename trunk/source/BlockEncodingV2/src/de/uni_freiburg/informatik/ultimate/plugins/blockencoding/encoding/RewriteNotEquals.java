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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDisequality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public final class RewriteNotEquals extends BaseBlockEncoder<IcfgLocation> {

	private final IcfgEdgeBuilder mEdgeBuilder;

	public RewriteNotEquals(final IcfgEdgeBuilder edgeBuilder, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final ILogger logger) {
		super(logger, services, backtranslator);
		mEdgeBuilder = edgeBuilder;
	}

	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		final IcfgEdgeIterator iter = new IcfgEdgeIterator(icfg);
		final Set<IcfgEdge> toRemove = new HashSet<>();
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();

		while (iter.hasNext()) {
			final IcfgEdge edge = iter.next();
			if (!(edge instanceof IIcfgInternalTransition<?>) || edge instanceof Summary) {
				continue;
			}
			final UnmodifiableTransFormula oldTransFormula = edge.getTransformula();
			final Term newTerm;
			{
				final Term withoutIte = new IteRemover(mgdScript).transform(oldTransFormula.getFormula());
				final Term inNnf = new NnfTransformer(mgdScript, mServices, QuantifierHandling.KEEP)
						.transform(withoutIte);
				newTerm = new RewriteDisequality.RewriteDisequalityTransformer(mgdScript.getScript()).transform(inNnf);
			}

			if (newTerm == oldTransFormula.getFormula()) {
				// formula unchanged, do not change edge
				continue;
			}

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Rewrote ");
				mLogger.debug(oldTransFormula.getFormula());
				mLogger.debug(newTerm);
			}
			if (!toRemove.add(edge)) {
				continue;
			}
			final UnmodifiableTransFormula newTransFormula = constructNewTransFormula(mgdScript, oldTransFormula,
					newTerm);
			final IcfgEdge newEdge = mEdgeBuilder.constructAndConnectInternalTransition(edge, edge.getSource(),
					edge.getTarget(), newTransFormula);
			rememberEdgeMapping(newEdge, edge);
		}

		toRemove.stream().forEach(a -> {
			a.disconnectSource();
			a.disconnectTarget();
		});
		mRemovedEdges = toRemove.size();
		return icfg;
	}

	private UnmodifiableTransFormula constructNewTransFormula(final ManagedScript mgScript,
			final UnmodifiableTransFormula oldTransFormula, final Term newTerm) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(oldTransFormula.getInVars(),
				oldTransFormula.getOutVars(), oldTransFormula.getNonTheoryConsts().isEmpty(),
				oldTransFormula.getNonTheoryConsts(), oldTransFormula.getBranchEncoders().isEmpty(),
				oldTransFormula.getBranchEncoders(), oldTransFormula.getAuxVars().isEmpty());
		tfb.setFormula(newTerm);
		tfb.addAuxVarsButRenameToFreshCopies(oldTransFormula.getAuxVars(), mgScript);
		tfb.setInfeasibility(oldTransFormula.isInfeasible());
		return tfb.finishConstruction(mgScript);
	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0;
	}
}
