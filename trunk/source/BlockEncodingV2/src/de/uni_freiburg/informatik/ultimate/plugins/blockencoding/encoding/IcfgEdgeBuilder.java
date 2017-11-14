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

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgEdgeBuilder {

	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;
	private final ManagedScript mManagedScript;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final IcfgEdgeFactory mEdgeFactory;

	public IcfgEdgeBuilder(final CfgSmtToolkit toolkit, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mManagedScript = toolkit.getManagedScript();
		mCfgSmtToolkit = toolkit;
		mEdgeFactory = toolkit.getIcfgEdgeFactory();
	}

	public IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IcfgEdge> edges) {
		return constructSequentialComposition(source, target, edges, false, false);
	}

	public IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IcfgEdge first, final IcfgEdge second) {
		final List<IcfgEdge> codeblocks = Arrays.asList(new IcfgEdge[] { first, second });
		return constructSequentialComposition(source, target, codeblocks, false, false);
	}

	public IcfgEdge constructSimplifiedSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IcfgEdge block) {
		return constructSequentialComposition(source, target, Collections.singletonList(block), true, true);
	}

	private IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IcfgEdge> transitions, final boolean simplify, final boolean elimQuants) {
		assert onlyInternal(transitions) : "You cannot have calls or returns in normal sequential compositions";
		final List<UnmodifiableTransFormula> transFormulas =
				transitions.stream().map(IcfgUtils::getTransformula).collect(Collectors.toList());
		final UnmodifiableTransFormula tf = TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript,
				simplify, elimQuants, false, mXnfConversionTechnique, mSimplificationTechnique, transFormulas);
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf);
		source.addOutgoing(rtr);
		target.addIncoming(rtr);
		ModelUtils.mergeAnnotations(transitions, rtr);
		return rtr;
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
						mXnfConversionTechnique, mSimplificationTechnique, symbolTable, modifiableGlobalsOfCallee);

		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf);
		source.addOutgoing(rtr);
		target.addIncoming(rtr);
		ModelUtils.mergeAnnotations(rtr, callTrans, intermediateTrans, returnTrans);
		return rtr;
	}

	public IcfgEdge constructParallelComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IcfgEdge> transitions) {
		assert onlyInternal(transitions) : "You cannot have calls or returns in normal sequential compositions";
		final List<UnmodifiableTransFormula> transFormulas =
				transitions.stream().map(IcfgUtils::getTransformula).collect(Collectors.toList());
		final UnmodifiableTransFormula[] tfArray =
				transFormulas.toArray(new UnmodifiableTransFormula[transFormulas.size()]);
		final int serialNumber = HashUtils.hashHsieh(293, (Object[]) tfArray);
		final UnmodifiableTransFormula parallelTf = TransFormulaUtils.parallelComposition(mLogger, mServices,
				serialNumber, mManagedScript, null, false, mXnfConversionTechnique, tfArray);
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, parallelTf);
		source.addOutgoing(rtr);
		target.addIncoming(rtr);
		ModelUtils.mergeAnnotations(transitions, rtr);
		return rtr;
	}

	private static boolean onlyInternal(final List<IcfgEdge> transitions) {
		return transitions.stream().allMatch(IcfgEdgeBuilder::onlyInternal);
	}

	private static boolean onlyInternal(final IcfgEdge transition) {
		return transition instanceof IIcfgInternalTransition<?> && !(transition instanceof Summary);
	}

	public IcfgEdge constructInternalTransition(final IcfgEdge oldTransition, final IcfgLocation source,
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
		return constructInternalTransition(oldTransition, source, target, tf);
	}

	public IcfgEdge constructInternalTransition(final IcfgEdge oldTransition, final IcfgLocation source,
			final IcfgLocation target, final UnmodifiableTransFormula tf) {
		assert onlyInternal(oldTransition) : "You cannot have calls or returns in normal sequential compositions";
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf);
		source.addOutgoing(rtr);
		target.addIncoming(rtr);
		ModelUtils.copyAnnotations(oldTransition, rtr);
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
