/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.ICompositionFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * Implements an {@link ICompositionFactory} that is suitable for Trace Abstraction. This class is used by
 * {@link PetriNetLargeBlockEncoding}.
 *
 * @author Elisabeth Schanno
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (sourceheizmann@informatik.uni-freiburg.de)
 *
 */
public class IcfgCompositionFactory implements IPLBECompositionFactory<IcfgEdge> {

	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	private final IcfgEdgeBuilder mEdgeBuilder;
	private final Map<IcfgEdge, TermVariable> mBranchEncoders;

	public IcfgCompositionFactory(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit) {
		mEdgeBuilder = new IcfgEdgeBuilder(cfgSmtToolkit, services, SIMPLIFICATION_TECHNIQUE);
		mBranchEncoders = new HashMap<>();
	}

	@Override
	public boolean isComposable(final IcfgEdge transition) {
		return transition instanceof IIcfgInternalTransition<?> && !(transition instanceof Summary);
	}

	private boolean isComposable(final List<IcfgEdge> transitions) {
		return transitions.stream().allMatch(this::isComposable);
	}

	@Override
	public IcfgEdge composeSequential(final IcfgEdge first, final IcfgEdge second) {
		// Simplify resulting TransFormula because various other algorithms in Ultimate
		// have to work with this term.
		final boolean simplify = true;
		// Try to eliminate auxiliary variables to avoid quantifier alterations in
		// subsequent SMT solver calls during verification.
		// TODO (Dominik 2020-12-02): Disabled due to timeout / OOM in old quantifier elimination (XnfTransformer).
		final boolean tryAuxVarElimination = false;

		final IcfgLocation source = first.getSource();
		final IcfgLocation target = second.getTarget();

		final List<IcfgEdge> transitions = Arrays.asList(first, second);
		assert isComposable(transitions) : "You cannot have calls or returns in sequential compositions";

		return mEdgeBuilder.constructSequentialComposition(source, target, transitions, simplify, tryAuxVarElimination,
				false);
	}

	@Override
	public IcfgEdge composeParallel(final List<IcfgEdge> transitions) {
		assert !transitions.isEmpty() : "Cannot compose 0 transitions";
		assert isComposable(transitions) : "You cannot have calls or returns in parallel compositions";

		final IcfgLocation source = transitions.get(0).getSource();
		final IcfgLocation target = transitions.get(0).getTarget();
		assert transitions.stream().allMatch(t -> t.getSource() == source
				&& t.getTarget() == target) : "Can only compose transitions with equal sources and targets.";

		final Map<TermVariable, IcfgEdge> branchIndicator2edge =
				mEdgeBuilder.constructBranchIndicatorToEdgeMapping(transitions);
		storeBranchEncoders(branchIndicator2edge);
		return mEdgeBuilder.constructParallelComposition(source, target, branchIndicator2edge);
	}

	private void storeBranchEncoders(final Map<TermVariable, IcfgEdge> indicators) {
		for (final Map.Entry<TermVariable, IcfgEdge> entry : indicators.entrySet()) {
			assert !mBranchEncoders.containsKey(entry.getValue()) : "Ambiguous branch encoder for transition";
			mBranchEncoders.put(entry.getValue(), entry.getKey());
		}
	}

	@Override
	public Map<IcfgEdge, TermVariable> getBranchEncoders() {
		return mBranchEncoders;
	}
}
