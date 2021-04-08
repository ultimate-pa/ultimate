/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.ICompositionFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

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
	private static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final IcfgEdgeBuilder mEdgeBuilder;
	private final Map<IcfgEdge, TermVariable> mBranchEncoders;

	public IcfgCompositionFactory(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit) {
		mEdgeBuilder = new IcfgEdgeBuilder(cfgSmtToolkit, services, SIMPLIFICATION_TECHNIQUE, XNF_CONVERSION_TECHNIQUE);
		mBranchEncoders = new HashMap<>();
	}

	/**
	 * Work around a problem that can happen with repeated Lipton reduction: When applying the choice rule, a formula
	 * with branch encoders is created. Then the Trace Abstraction may cause the composed transition to be duplicated
	 * with different predicates as pre- or postconditions. If we then compose the two duplicated transitions they will
	 * both have the same branch encoders and thus the resulting formula will only allow a subset of the original
	 * traces. To prevent this, we must not compose transitions with the same branch encoders.
	 *
	 * @param t1
	 *            The first transition.
	 * @param t2
	 *            The second transition.
	 * @return false if the branch encoders prevent composition. true otherwise.
	 */
	private static boolean checkBranchEncoders(final IcfgEdge t1, final IcfgEdge t2) {
		return !(t1 instanceof IActionWithBranchEncoders && t2 instanceof IActionWithBranchEncoders
				&& DataStructureUtils.haveNonEmptyIntersection(
						((IActionWithBranchEncoders) t1).getTransitionFormulaWithBranchEncoders().getBranchEncoders(),
						((IActionWithBranchEncoders) t2).getTransitionFormulaWithBranchEncoders().getBranchEncoders()));
	}

	private static boolean isComposable(final IcfgEdge transition) {
		return transition instanceof IIcfgInternalTransition<?> && !(transition instanceof Summary);
	}

	private static boolean isComposable(final List<IcfgEdge> transitions) {
		return transitions.stream().allMatch(IcfgCompositionFactory::isComposable);
	}

	@Override
	public boolean isSequentiallyComposable(final IcfgEdge t1, final IcfgEdge t2) {
		return isComposable(t1) && isComposable(t2) && t1.getTarget() == t2.getSource() && checkBranchEncoders(t1, t2);
	}

	@Override
	public boolean isParallelyComposable(final List<IcfgEdge> letters) {
		final IcfgLocation source = letters.get(0).getSource();
		final IcfgLocation target = letters.get(0).getTarget();
		return letters.stream().allMatch(t -> isComposable(t) && t.getSource() == source && t.getTarget() == target
				&& letters.stream().allMatch(t2 -> t == t2 || checkBranchEncoders(t, t2)));
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
