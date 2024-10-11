/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;

/**
 * A factory that can create copies of {@link IcfgEdge} instances with new transition formulas.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class IcfgCopyFactory implements ICopyActionFactory<IcfgEdge> {
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	private final IcfgEdgeBuilder mEdgeBuilder;

	public IcfgCopyFactory(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit) {
		mEdgeBuilder = new IcfgEdgeBuilder(cfgSmtToolkit, services, SIMPLIFICATION_TECHNIQUE);
	}

	@Override
	public IcfgEdge copy(final IcfgEdge original, final UnmodifiableTransFormula newTransformula,
			final UnmodifiableTransFormula newTransformulaWithBE) {
		if (newTransformulaWithBE == null) {
			if (original instanceof IcfgForkThreadCurrentTransition) {
				return mEdgeBuilder.constructForkCurrentTransition((IcfgForkThreadCurrentTransition) original,
						newTransformula, false);
			}
			if (original instanceof IcfgForkThreadOtherTransition) {
				return mEdgeBuilder.constructForkOtherTransition((IcfgForkThreadOtherTransition) original,
						newTransformula, false);
			}
			if (original instanceof IcfgJoinThreadCurrentTransition) {
				return mEdgeBuilder.constructJoinCurrentTransition((IcfgJoinThreadCurrentTransition) original,
						newTransformula, false);
			}
			if (original instanceof IcfgJoinThreadOtherTransition) {
				return mEdgeBuilder.constructJoinOtherTransition((IcfgJoinThreadOtherTransition) original,
						newTransformula, false);
			}
			return mEdgeBuilder.constructInternalTransition(original, original.getSource(), original.getTarget(),
					newTransformula);
		}

		if (!(original instanceof IActionWithBranchEncoders)) {
			throw new IllegalArgumentException(
					"TF with branch encoders given for action without branch encoders: " + original);
		}
		return mEdgeBuilder.constructInternalTransition(original, original.getSource(), original.getTarget(),
				newTransformula, newTransformulaWithBE, false);
	}
}
