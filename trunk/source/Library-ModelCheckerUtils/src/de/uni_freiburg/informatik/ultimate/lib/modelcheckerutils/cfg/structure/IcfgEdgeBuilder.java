/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgEdgeBuilder {

	private final SimplificationTechnique mSimplificationTechnique;
	private final ManagedScript mManagedScript;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final IcfgEdgeFactory mEdgeFactory;

	public IcfgEdgeBuilder(final CfgSmtToolkit toolkit, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mManagedScript = toolkit.getManagedScript();
		mCfgSmtToolkit = toolkit;
		mEdgeFactory = toolkit.getIcfgEdgeFactory();
	}

	public IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IcfgEdge> edges) {
		return constructSequentialComposition(source, target, edges, false, false, true);
	}

	public IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IcfgEdge first, final IcfgEdge second) {
		final List<IcfgEdge> codeblocks = Arrays.asList(new IcfgEdge[] { first, second });
		return constructSequentialComposition(source, target, codeblocks, false, false, true);
	}

	public IcfgEdge constructSimplifiedSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IcfgEdge block) {
		return constructSequentialComposition(source, target, Collections.singletonList(block), true, true, true);
	}

	public IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IcfgEdge> transitions, final boolean simplify, final boolean elimQuants, final boolean connect) {
		assert onlyInternal(transitions) : "You cannot have calls or returns in normal sequential compositions";

		final List<UnmodifiableTransFormula> transFormulas =
				transitions.stream().map(IcfgUtils::getTransformula).collect(Collectors.toList());
		final UnmodifiableTransFormula tf = TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript,
				simplify, elimQuants, false, mSimplificationTechnique, transFormulas);

		final List<UnmodifiableTransFormula> transFormulasWithBE =
				transitions.stream().map(IcfgEdgeBuilder::getTransformulaWithBE).collect(Collectors.toList());
		final UnmodifiableTransFormula tfWithBE =
				TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, simplify, elimQuants, false,
						mSimplificationTechnique, transFormulasWithBE);

		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf, tfWithBE);
		ModelUtils.mergeAnnotations(transitions, rtr);

		if (connect) {
			source.addOutgoing(rtr);
			target.addIncoming(rtr);
		}
		return rtr;
	}

	private static UnmodifiableTransFormula getTransformulaWithBE(final IcfgEdge edge) {
		if (edge instanceof IActionWithBranchEncoders) {
			return ((IActionWithBranchEncoders) edge).getTransitionFormulaWithBranchEncoders();
		}
		return edge.getTransformula();
	}

	public IcfgEdge constructInterproceduralSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgCallTransition<?> callTrans, final IIcfgTransition<?> intermediateTrans,
			final IIcfgReturnTransition<?, ?> returnTrans) {
		return constructInterproceduralSequentialComposition(source, target, callTrans, intermediateTrans, returnTrans,
				false, false);
	}

	private IcfgEdge constructInterproceduralSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgCallTransition<?> callTrans, final IIcfgTransition<?> intermediateTrans,
			final IIcfgReturnTransition<?, ?> returnTrans, final boolean simplify, final boolean elimQuants) {

		final String calledProc = callTrans.getSucceedingProcedure();
		final UnmodifiableTransFormula callTf = callTrans.getLocalVarsAssignment();
		final UnmodifiableTransFormula oldVarsAssignment =
				mCfgSmtToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProc);
		final UnmodifiableTransFormula globalVarsAssignment =
				mCfgSmtToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProc);
		final UnmodifiableTransFormula procedureTf = intermediateTrans.getTransformula();
		final UnmodifiableTransFormula returnTf = returnTrans.getAssignmentOfReturn();
		final IIcfgSymbolTable symbolTable = mCfgSmtToolkit.getSymbolTable();
		final Set<IProgramNonOldVar> modifiableGlobalsOfCallee =
				mCfgSmtToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProc);
		final UnmodifiableTransFormula tf =
				TransFormulaUtils.sequentialCompositionWithCallAndReturn(mManagedScript, simplify, elimQuants, false,
						callTf, oldVarsAssignment, globalVarsAssignment, procedureTf, returnTf, mLogger, mServices,
						mSimplificationTechnique, symbolTable, modifiableGlobalsOfCallee);

		final UnmodifiableTransFormula tfWithBE;
		if (intermediateTrans instanceof IActionWithBranchEncoders) {
			final UnmodifiableTransFormula procedureTfWithBE =
					((IActionWithBranchEncoders) intermediateTrans).getTransitionFormulaWithBranchEncoders();
			tfWithBE = TransFormulaUtils.sequentialCompositionWithCallAndReturn(mManagedScript, simplify, elimQuants,
					false, callTf, oldVarsAssignment, globalVarsAssignment, procedureTfWithBE, returnTf, mLogger,
					mServices, mSimplificationTechnique, symbolTable, modifiableGlobalsOfCallee);
		} else {
			tfWithBE = tf;
		}

		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf, tfWithBE);
		source.addOutgoing(rtr);
		target.addIncoming(rtr);
		ModelUtils.mergeAnnotations(rtr, callTrans, intermediateTrans, returnTrans);
		return rtr;
	}

	/**
	 * Constructs the parallel composition of the given edges. Note that the new edge is NOT connected to the source and
	 * target locations.
	 *
	 * @param source
	 *            The source location for the parallel composition
	 * @param target
	 *            The target location for the parallel composition
	 * @param branchEncodersAndTransitions
	 *            A mapping from branch encoder variables to the corresponding edge. You can use
	 *            {@link constructBranchIndicatorToEdgeMapping} to create such a map.
	 * @return A new internal transition representing the parallel composition of the input edges.
	 */
	public IcfgInternalTransition constructParallelComposition(final IcfgLocation source, final IcfgLocation target,
			final Map<TermVariable, IcfgEdge> branchEncodersAndTransitions) {
		assert !branchEncodersAndTransitions.isEmpty() : "Cannot compose 0 transitions";

		final Collection<IcfgEdge> transitions = branchEncodersAndTransitions.values();
		assert onlyInternal(transitions) : "You cannot have calls or returns in parallel compositions";
		final boolean isInternal = true;

		final List<UnmodifiableTransFormula> transFormulas =
				transitions.stream().map(IcfgUtils::getTransformula).collect(Collectors.toList());
		final UnmodifiableTransFormula[] tfArray =
				transFormulas.toArray(new UnmodifiableTransFormula[transFormulas.size()]);
		final UnmodifiableTransFormula parallelTf = TransFormulaUtils.parallelComposition(mLogger, mServices,
				mManagedScript, null, false, isInternal, tfArray);

		final List<UnmodifiableTransFormula> transFormulasWithBE =
				transitions.stream().map(IcfgEdgeBuilder::getTransformulaWithBE).collect(Collectors.toList());
		final UnmodifiableTransFormula[] tfWithBEArray =
				transFormulasWithBE.toArray(new UnmodifiableTransFormula[transFormulasWithBE.size()]);
		final TermVariable[] branchIndicatorArray =
				branchEncodersAndTransitions.keySet().toArray(new TermVariable[branchEncodersAndTransitions.size()]);
		final UnmodifiableTransFormula parallelWithBranchIndicators =
				TransFormulaUtils.parallelComposition(mLogger, mServices, mManagedScript, branchIndicatorArray, false,
						isInternal, tfWithBEArray);

		final IcfgInternalTransition rtr =
				mEdgeFactory.createInternalTransition(source, target, null, parallelTf, parallelWithBranchIndicators);
		ModelUtils.mergeAnnotations(transitions, rtr);
		return rtr;
	}

	/**
	 * Creates fresh branch encoders for the given transitions. The returned map can be used with
	 * {@code constructParallelComposition(IcfgLocation, IcfgLocation, Map<TermVariable, IcfgEdge>}.
	 *
	 * @param transitions
	 *            A list of transitions
	 * @return A mapping from fresh branch encoder variables to the given transitions.
	 */
	public Map<TermVariable, IcfgEdge> constructBranchIndicatorToEdgeMapping(final List<IcfgEdge> transitions) {
		final LinkedHashMap<TermVariable, IcfgEdge> result = new LinkedHashMap<>();
		mManagedScript.lock(result);
		for (int i = 0; i < transitions.size(); i++) {
			final String varname = "BraInd" + i + "of" + transitions.size();
			final Sort boolSort = SmtSortUtils.getBoolSort(mManagedScript.getScript());
			final TermVariable tv = mManagedScript.constructFreshTermVariable(varname, boolSort);
			result.put(tv, transitions.get(i));
		}
		mManagedScript.unlock(result);
		return result;
	}

	private static boolean onlyInternal(final Collection<IcfgEdge> transitions) {
		return transitions.stream().allMatch(IcfgEdgeBuilder::onlyInternal);
	}

	private static boolean onlyInternal(final IcfgEdge transition) {
		return transition instanceof IIcfgInternalTransition<?> && !(transition instanceof IIcfgSummaryTransition<?>);
	}

	public IcfgEdge constructAndConnectInternalTransition(final IcfgEdge oldTransition, final IcfgLocation source,
			final IcfgLocation target, final Term term) {
		assert onlyInternal(oldTransition) : "You cannot have calls or returns in normal sequential compositions";
		final UnmodifiableTransFormula oldTf = IcfgUtils.getTransformula(oldTransition);

		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(term.getFreeVars()));
		final Set<TermVariable> oldFreeVars = new HashSet<>(Arrays.asList(oldTf.getFormula().getFreeVars()));

		final Map<IProgramVar, TermVariable> newInVars = filterValues(oldTf.getInVars(), freeVars::contains);
		final Map<IProgramVar, TermVariable> newOutVars = filterValues(oldTf.getOutVars(), freeVars::contains);
		final Set<TermVariable> newAuxVars = new HashSet<>(oldTf.getAuxVars());
		newAuxVars.retainAll(freeVars);

		newInVars.putAll(filterValues(oldTf.getInVars(), a -> !oldFreeVars.contains(a)));
		newOutVars.putAll(filterValues(oldTf.getOutVars(), a -> !oldFreeVars.contains(a)));

		final TransFormulaBuilder tfb = new TransFormulaBuilder(newInVars, newOutVars,
				oldTf.getNonTheoryConsts().isEmpty(), oldTf.getNonTheoryConsts(), true, null, newAuxVars.isEmpty());
		tfb.setFormula(term);
		if (!newAuxVars.isEmpty()) {
			tfb.addAuxVarsButRenameToFreshCopies(newAuxVars, mManagedScript);
		}

		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);

		final UnmodifiableTransFormula tf = tfb.finishConstruction(mManagedScript);
		return constructAndConnectInternalTransition(oldTransition, source, target, tf);
	}

	public IcfgEdge constructAndConnectInternalTransition(final IcfgEdge oldTransition, final IcfgLocation source,
			final IcfgLocation target, final UnmodifiableTransFormula tf) {
		final IcfgEdge edge = constructInternalTransition(oldTransition, source, target, tf);
		source.addOutgoing(edge);
		target.addIncoming(edge);
		return edge;
	}

	public IcfgEdge constructInternalTransition(final IcfgEdge oldTransition, final IcfgLocation source,
			final IcfgLocation target, final UnmodifiableTransFormula tf) {
		assert onlyInternal(oldTransition) : "You cannot have calls or returns in normal sequential compositions";
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf);
		ModelUtils.copyAnnotations(oldTransition, rtr);
		return rtr;
	}

	public IcfgForkThreadCurrentTransition constructForkCurrentTransition(
			final IcfgForkThreadCurrentTransition oldTransition, final UnmodifiableTransFormula tf,
			final boolean connect) {
		final IcfgForkThreadCurrentTransition rtr =
				mEdgeFactory.createForkThreadCurrentTransition(oldTransition.getSource(), oldTransition.getTarget(),
						null, tf, oldTransition.getForkSmtArguments(), oldTransition.getNameOfForkedProcedure());
		ModelUtils.copyAnnotations(oldTransition, rtr);
		if (connect) {
			oldTransition.getSource().addOutgoing(rtr);
			oldTransition.getTarget().addIncoming(rtr);
		}
		return rtr;
	}

	public IcfgForkThreadOtherTransition constructForkOtherTransition(final IcfgForkThreadOtherTransition oldTransition,
			final UnmodifiableTransFormula tf, final boolean connect) {
		final IcfgForkThreadOtherTransition rtr =
				mEdgeFactory.createForkThreadOtherTransition(oldTransition.getSource(), oldTransition.getTarget(), null,
						tf, oldTransition.getCorrespondingIIcfgForkTransitionCurrentThread());
		ModelUtils.copyAnnotations(oldTransition, rtr);
		if (connect) {
			oldTransition.getSource().addOutgoing(rtr);
			oldTransition.getTarget().addIncoming(rtr);
		}
		return rtr;
	}

	public IcfgJoinThreadCurrentTransition constructJoinCurrentTransition(
			final IcfgJoinThreadCurrentTransition oldTransition, final UnmodifiableTransFormula tf,
			final boolean connect) {
		final IcfgJoinThreadCurrentTransition rtr = mEdgeFactory.createJoinThreadCurrentTransition(
				oldTransition.getSource(), oldTransition.getTarget(), null, tf, oldTransition.getJoinSmtArguments());
		ModelUtils.copyAnnotations(oldTransition, rtr);
		if (connect) {
			oldTransition.getSource().addOutgoing(rtr);
			oldTransition.getTarget().addIncoming(rtr);
		}
		return rtr;
	}

	public IcfgJoinThreadOtherTransition constructJoinOtherTransition(final IcfgJoinThreadOtherTransition oldTransition,
			final UnmodifiableTransFormula tf, final boolean connect) {
		final IcfgJoinThreadOtherTransition rtr =
				mEdgeFactory.createJoinThreadOtherTransition(oldTransition.getSource(), oldTransition.getTarget(), null,
						tf, oldTransition.getCorrespondingIIcfgJoinTransitionCurrentThread());
		ModelUtils.copyAnnotations(oldTransition, rtr);
		if (connect) {
			oldTransition.getSource().addOutgoing(rtr);
			oldTransition.getTarget().addIncoming(rtr);
		}
		return rtr;
	}

	public IcfgEdge constructInternalTransition(final IcfgEdge oldTransition, final IcfgLocation source,
			final IcfgLocation target, final UnmodifiableTransFormula tf, final UnmodifiableTransFormula tfWithBe,
			final boolean connect) {
		assert onlyInternal(oldTransition) : "You cannot have calls or returns in normal sequential compositions";
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf, tfWithBe);
		ModelUtils.copyAnnotations(oldTransition, rtr);
		if (connect) {
			source.addOutgoing(rtr);
			target.addIncoming(rtr);
		}
		return rtr;
	}

	private static <K, V> Map<K, V> filterValues(final Map<K, V> map, final Predicate<V> funValueTest) {
		if (map == null) {
			return Collections.emptyMap();
		}
		return map.entrySet().stream().filter(a -> funValueTest.test(a.getValue()))
				.collect(Collectors.toMap(Entry<K, V>::getKey, Entry<K, V>::getValue));
	}
}
