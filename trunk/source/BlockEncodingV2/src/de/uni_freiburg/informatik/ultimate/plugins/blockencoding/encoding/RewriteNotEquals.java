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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.NNF;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDisequality;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteIte;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TransitionPreprocessor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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
		final CfgSmtToolkit toolkit = icfg.getCfgSmtToolkit();
		final ManagedScript mgScript = toolkit.getManagedScript();
		final ReplacementVarFactory repVarFac = new ReplacementVarFactory(toolkit, false);
		final List<TransitionPreprocessor> transformer = new ArrayList<>();
		transformer.add(new RewriteIte());
		transformer.add(new NNF(mServices));
		transformer.add(new RemoveNegation());
		transformer.add(new RewriteDisequality());
		transformer.add(new NNF(mServices));
		transformer.add(new RemoveNegation());

		while (iter.hasNext()) {
			final IcfgEdge edge = iter.next();
			if (!(edge instanceof IIcfgInternalTransition<?>) || edge instanceof Summary) {
				continue;
			}

			final ModifiableTransFormula mtf =
					ModifiableTransFormulaUtils.buildTransFormula(IcfgUtils.getTransformula(edge), repVarFac, mgScript);
			final ModifiableTransFormula rewrittenMtf = rewrite(transformer, mtf, mgScript);
			if (mtf.getFormula().equals(rewrittenMtf.getFormula())) {
				// nothing to do
				continue;
			}
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Rewrote ");
				mLogger.debug(mtf.getFormula());
				mLogger.debug(rewrittenMtf.getFormula());
			}
			if (!toRemove.add(edge)) {
				continue;
			}
			final IcfgEdge newEdge = mEdgeBuilder.constructInternalTransition(edge, edge.getSource(), edge.getTarget(),
					TransFormulaBuilder.constructCopy(mgScript, rewrittenMtf, Collections.emptySet(),
							Collections.emptySet(), Collections.emptyMap()));
			rememberEdgeMapping(newEdge, edge);
		}

		if (!repVarFac.isUnused()) {
			final CfgSmtToolkit newToolkit = new CfgSmtToolkit(repVarFac.constructModifiableGlobalsTable(), mgScript,
					repVarFac.constructIIcfgSymbolTable(), toolkit.getProcedures(), toolkit.getInParams(),
					toolkit.getOutParams(), toolkit.getIcfgEdgeFactory(), toolkit.getConcurrencyInformation(),
					toolkit.getSmtSymbols());
			icfg.setCfgSmtToolkit(newToolkit);
		}

		toRemove.stream().forEach(a -> {
			a.disconnectSource();
			a.disconnectTarget();
		});
		mRemovedEdges = toRemove.size();
		return icfg;
	}

	private static ModifiableTransFormula rewrite(final List<TransitionPreprocessor> transformers,
			final ModifiableTransFormula mtf, final ManagedScript mgdScript) {
		ModifiableTransFormula rtr = mtf;
		for (final TransitionPreprocessor transformer : transformers) {
			try {
				rtr = transformer.process(mgdScript, rtr);
			} catch (final TermException e) {
				throw new RuntimeException(e);
			}
		}
		return rtr;
	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0;
	}
}
