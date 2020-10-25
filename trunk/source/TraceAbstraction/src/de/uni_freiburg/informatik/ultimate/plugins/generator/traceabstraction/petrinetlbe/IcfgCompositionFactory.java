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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.ICompositionFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;

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

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final IcfgEdgeFactory mEdgeFactory;
	private final Map<IcfgEdge, TermVariable> mBranchEncoders;

	public IcfgCompositionFactory(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mManagedScript = cfgSmtToolkit.getManagedScript();
		mEdgeFactory = cfgSmtToolkit.getIcfgEdgeFactory();
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
		final boolean tryAuxVarElimination = true;

		final IcfgLocation source = first.getSource();
		final IcfgLocation target = second.getTarget();

		final List<IcfgEdge> transitions = Arrays.asList(first, second);
		assert isComposable(transitions) : "You cannot have calls or returns in sequential compositions";

		// TODO This partially duplicates code in IcfgEdgeBuilder
		final List<UnmodifiableTransFormula> transFormulas =
				transitions.stream().map(IcfgUtils::getTransformula).collect(Collectors.toList());
		final UnmodifiableTransFormula tf =
				TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, simplify,
						tryAuxVarElimination, false, XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE, transFormulas);

		final UnmodifiableTransFormula tfWithBE;
		if (first instanceof IActionWithBranchEncoders || second instanceof IActionWithBranchEncoders) {
			final UnmodifiableTransFormula tf1 = getTransformulaWithBE(first);
			final UnmodifiableTransFormula tf2 = getTransformulaWithBE(second);
			tfWithBE = TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, simplify,
					tryAuxVarElimination, false, XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE,
					Arrays.asList(tf1, tf2));
		} else {
			tfWithBE = tf;
		}
		final IcfgEdge rtr = mEdgeFactory.createInternalTransition(source, target, null, tf, tfWithBE);
		ModelUtils.mergeAnnotations(transitions, rtr);

		return rtr;
	}

	private UnmodifiableTransFormula getTransformulaWithBE(final IcfgEdge edge) {
		if (edge instanceof IActionWithBranchEncoders) {
			return ((IActionWithBranchEncoders) edge).getTransitionFormulaWithBranchEncoders();
		}
		return edge.getTransformula();
	}

	@Override
	// TODO This method partially duplicates code in IcfgEdgeBuilder
	public IcfgEdge composeParallel(final List<IcfgEdge> transitions) {
		assert !transitions.isEmpty() : "Cannot compose 0 transitions";
		assert isComposable(transitions) : "You cannot have calls or returns in parallel compositions";

		final IcfgLocation source = transitions.get(0).getSource();
		final IcfgLocation target = transitions.get(0).getTarget();
		assert transitions.stream().allMatch(t -> t.getSource() == source
				&& t.getTarget() == target) : "Can only compose transitions with equal sources and targets.";

		final List<UnmodifiableTransFormula> transFormulas =
				transitions.stream().map(IcfgUtils::getTransformula).collect(Collectors.toList());
		final UnmodifiableTransFormula[] tfArray =
				transFormulas.toArray(new UnmodifiableTransFormula[transFormulas.size()]);
		final UnmodifiableTransFormula parallelTf = TransFormulaUtils.parallelComposition(mLogger, mServices,
				mManagedScript, null, false, XNF_CONVERSION_TECHNIQUE, tfArray);

		final List<UnmodifiableTransFormula> transFormulasWithBE =
				transitions.stream().map(this::getTransformulaWithBE).collect(Collectors.toList());
		final UnmodifiableTransFormula[] tfWithBEArray =
				transFormulasWithBE.toArray(new UnmodifiableTransFormula[transFormulasWithBE.size()]);
		final LinkedHashMap<TermVariable, IcfgEdge> branchIndicator2edge =
				constructBranchIndicatorToEdgeMapping(parallelTf.hashCode(), mManagedScript, transitions);
		final TermVariable[] branchIndicatorArray =
				branchIndicator2edge.keySet().toArray(new TermVariable[branchIndicator2edge.size()]);
		final UnmodifiableTransFormula parallelWithBranchIndicators = TransFormulaUtils.parallelComposition(mLogger,
				mServices, mManagedScript, branchIndicatorArray, false, XNF_CONVERSION_TECHNIQUE, tfWithBEArray);

		final IcfgEdge rtr =
				mEdgeFactory.createInternalTransition(source, target, null, parallelTf, parallelWithBranchIndicators);
		ModelUtils.mergeAnnotations(transitions, rtr);

		// Update info for back translation
		storeBranchEncoders(branchIndicator2edge);

		return rtr;
	}

	private static LinkedHashMap<TermVariable, IcfgEdge> constructBranchIndicatorToEdgeMapping(final int serialNumber,
			final ManagedScript managedScript, final List<IcfgEdge> transitions) {
		final LinkedHashMap<TermVariable, IcfgEdge> result = new LinkedHashMap<>();
		managedScript.lock(result);
		for (int i = 0; i < transitions.size(); i++) {
			final String varname = "BraInd" + i + "of" + serialNumber;
			final Sort boolSort = SmtSortUtils.getBoolSort(managedScript.getScript());
			final TermVariable tv = managedScript.constructFreshTermVariable(varname, boolSort);
			result.put(tv, transitions.get(i));
		}
		managedScript.unlock(result);
		return result;
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
