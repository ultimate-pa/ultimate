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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.BranchEncoderRenaming;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Implements an {@link ICompositionFactory} that is suitable for Trace Abstraction. This class is used by
 * {@link PetriNetLargeBlockEncoding}.
 *
 * @author Elisabeth Schanno
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IcfgCompositionFactory implements IPLBECompositionFactory<IcfgEdge> {

	// Simplify composed TransFormula because various other algorithms in Ultimate have to work with this term.
	private static final boolean SIMPLIFY_SEQ_COMP = true;
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	// Try to eliminate auxiliary variables to avoid quantifier alternations in subsequent SMT solver calls during
	// verification.
	// TODO (Dominik 2020-12-02): Disabled due to timeout / OOM in old quantifier elimination (XnfTransformer).
	private static final boolean TRY_AUX_VAR_ELIMINATION = false;
	private static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final IcfgEdgeBuilder mEdgeBuilder;

	// Branch encoders introduced in parallel compositions (mapping from each input edge to its branch encoder)
	private final Map<IcfgEdge, TermVariable> mBranchEncoders = new HashMap<>();

	// In sequential compositions of edges with shared branch encoders, we must rename branch encoders in one of the
	// edges. Here we map a composed edge to the branch encoder renaming used for the first argument of the composition.
	private final Map<IcfgEdge, BranchEncoderRenaming> mBranchEncoderRenamingInFirst = new HashMap<>();

	public IcfgCompositionFactory(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit) {
		mLogger = services.getLoggingService().getLogger(IcfgCompositionFactory.class);
		mMgdScript = cfgSmtToolkit.getManagedScript();
		mEdgeBuilder = new IcfgEdgeBuilder(cfgSmtToolkit, services, SIMPLIFICATION_TECHNIQUE, XNF_CONVERSION_TECHNIQUE);
	}

	@Override
	public boolean isSequentiallyComposable(final IcfgEdge t1, final IcfgEdge t2) {
		// At the moment, we require target and source to coincide, i.e., we prevent compositions across threads.
		// While such compositions may be desirable (they overcome a shortcoming of normal Lipton reduction), major
		// refactoring is probably needed to support them: Since the composition must be an IcfgEdge, we must assign it
		// some source and target locations, which would be unclear with such mixed-thread compositions.
		return isComposable(t1) && isComposable(t2); // && t1.getTarget() == t2.getSource();
	}

	@Override
	public boolean isParallelyComposable(final List<IcfgEdge> letters) {
		assert !letters.isEmpty() : "Cannot compose 0 transitions";
		final IcfgLocation source = letters.get(0).getSource();
		final IcfgLocation target = letters.get(0).getTarget();
		return letters.stream().allMatch(t -> isComposable(t) && t.getSource() == source && t.getTarget() == target);
	}

	private static boolean isComposable(final IcfgEdge transition) {
		return transition instanceof IIcfgInternalTransition<?> && !(transition instanceof Summary);
	}

	@Override
	public IcfgEdge composeSequential(final IcfgEdge first, final IcfgEdge second) {
		assert isSequentiallyComposable(first, second) : "Illegal sequential composition: " + first + " and " + second;
		if (first.getTarget() != second.getSource()) {
			mLogger.error("Composing non-subsequent actions: " + first + " and " + second);
		}

		final BranchEncoderRenaming branchEncoderRenaming;
		final IcfgEdge renamedFirst;
		if (shareBranchEncoders(first, second)) {
			branchEncoderRenaming = BranchEncoderRenaming.makeFresh((IActionWithBranchEncoders) first, mMgdScript);
			renamedFirst = branchEncoderRenaming.applyToIcfgEdge(first, mMgdScript, mEdgeBuilder);
		} else {
			branchEncoderRenaming = null;
			renamedFirst = first;
		}

		final IcfgEdge composition = mEdgeBuilder.constructSequentialComposition(first.getSource(), second.getTarget(),
				Arrays.asList(renamedFirst, second), SIMPLIFY_SEQ_COMP, TRY_AUX_VAR_ELIMINATION, false);

		if (branchEncoderRenaming != null) {
			// remember the branch encoder renaming used in this composition
			mBranchEncoderRenamingInFirst.put(composition, branchEncoderRenaming);
		}

		return composition;
	}

	private static boolean shareBranchEncoders(final IcfgEdge t1, final IcfgEdge t2) {
		return t1 instanceof IActionWithBranchEncoders && t2 instanceof IActionWithBranchEncoders
				&& DataStructureUtils.haveNonEmptyIntersection(
						((IActionWithBranchEncoders) t1).getTransitionFormulaWithBranchEncoders().getBranchEncoders(),
						((IActionWithBranchEncoders) t2).getTransitionFormulaWithBranchEncoders().getBranchEncoders());
	}

	@Override
	public IcfgEdge composeParallel(final List<IcfgEdge> transitions) {
		assert isParallelyComposable(transitions) : "Illegal parallel composition: " + transitions;

		final IcfgLocation source = transitions.get(0).getSource();
		final IcfgLocation target = transitions.get(0).getTarget();

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

	@Override
	public Map<IcfgEdge, BranchEncoderRenaming> getBranchEncoderRenamings() {
		return mBranchEncoderRenamingInFirst;
	}
}
