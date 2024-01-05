/*
 * Copyright (C) 2024 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * This class provides as method for removing variables from the CFG's
 * {@link TransFormula}s outVars that are never read.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */

public class LiveIcfgUtils {

	private LiveIcfgUtils() {
		// do not instantiate
	}

	/**
	 * Remove from the CFG's {@link TransFormula}s the outVars that are local and
	 * never read. (Cannot remove global vars since they might be needed for our
	 * interprocedural proofs.)
	 */
	public static <LOC extends IcfgLocation> void applyFutureLiveOptimization(final IUltimateServiceProvider services,
			final IIcfg<LOC> icfg) {
		final HashRelation<IcfgLocation, IProgramVar> liveVarMap = computeFutureLiveVariables(icfg);
		updateTransFormulas(services, icfg, liveVarMap);
	}

	/**
	 * Collect all edges of a procedure. Here, this includes
	 * {@link IIcfgCallTransition}s whose target is in the current procedure and
	 * {@link IIcfgReturnTransition}s whose target is in the current procedure.
	 */
	private static <LOC extends IcfgLocation> Set<IcfgEdge> collectEdges(final Map<DebugIdentifier, LOC> pps) {
		final Set<IcfgEdge> result = new HashSet<>();
		for (final Entry<DebugIdentifier, LOC> pp : pps.entrySet()) {
			result.addAll(pp.getValue().getIncomingEdges());
		}
		return result;
	}

	private static <LOC extends IcfgLocation> HashRelation<IcfgLocation, IProgramVar> computeFutureLiveVariables(
			final IIcfg<LOC> icfg) {
		final HashRelation<IcfgLocation, IProgramVar> result = new HashRelation<>();
		final ArrayDeque<IcfgEdge> worklist = new ArrayDeque<>();
		initializeMapAndWorklist(icfg, worklist, result);
		doFixpointIteration(icfg, worklist, result);
		return result;
	}

	private static <LOC extends IcfgLocation> void updateTransFormulas(final IUltimateServiceProvider services,
			final IIcfg<LOC> icfg, final HashRelation<IcfgLocation, IProgramVar> futureLiveVarsMap) {
		int removedNonLiveVars = 0;
		for (final Entry<String, Map<DebugIdentifier, LOC>> procToPps : icfg.getProgramPoints().entrySet()) {
			final String proc = procToPps.getKey();
			// We must never remove inParams or modified globals (and their oldvars) that
			// are future live at the entry. These variables are needed in interprocedural
			// proofs.
			final Set<IProgramVar> indispensibleLocalVars = new HashSet<>();
			final Set<IProgramVar> futureLiveAtEntry = futureLiveVarsMap
					.getImage(icfg.getProcedureEntryNodes().get(proc));
			final List<ILocalProgramVar> inParams = icfg.getCfgSmtToolkit().getInParams().get(proc);
			for (final ILocalProgramVar inParam : inParams) {
				if (futureLiveAtEntry.contains(inParam)) {
					indispensibleLocalVars.add(inParam);
				}
			}

			final Set<IcfgEdge> edges = collectEdges(procToPps.getValue());
			for (final IcfgEdge edge : edges) {
				final IcfgLocation target = edge.getTarget();
				final Set<IProgramVar> futureLiveVars = futureLiveVarsMap.getImage(target);
				final TransFormula tf = edge.getTransformula();
				final Set<IProgramVar> outVarsToRemove = new HashSet<>(tf.getOutVars().keySet());
				outVarsToRemove.removeAll(futureLiveVars);
				outVarsToRemove.removeAll(indispensibleLocalVars);
				{
					// remove all global vars, they might be needed for our interprocedural proofs.
					// TODO: optimization only needed if they are past-live at the call
					final Iterator<IProgramVar> it = outVarsToRemove.iterator();
					while (it.hasNext()) {
						final IProgramVar elem = it.next();
						if (elem.isGlobal()) {
							it.remove();
						}
					}
				}
				if (!outVarsToRemove.isEmpty()) {
					removedNonLiveVars += outVarsToRemove.size();
					final boolean eliminateAuxVars = false;
					final UnmodifiableTransFormula liveTf;
					if (eliminateAuxVars) {
						final UnmodifiableTransFormula tmp = TransFormulaBuilder.constructCopy(
								icfg.getCfgSmtToolkit().getManagedScript(), tf, Collections.emptySet(), outVarsToRemove,
								Collections.emptyMap());
						liveTf = eliminateAuxVars(services, tmp, icfg.getCfgSmtToolkit().getManagedScript());
					} else {
						liveTf = TransFormulaBuilder.constructCopy(icfg.getCfgSmtToolkit().getManagedScript(), tf,
								Collections.emptySet(), outVarsToRemove, Collections.emptyMap());

					}

					final CodeBlock cb = (CodeBlock) edge;
					cb.setTransitionFormula(liveTf);
				}
			}
		}
		services.getLoggingService().getLogger(LiveIcfgUtils.class).log(LogLevel.INFO,
				String.format("Removed %s outVars from TransFormulas that were not future-live.", removedNonLiveVars));
	}

	private static UnmodifiableTransFormula eliminateAuxVars(final IUltimateServiceProvider services,
			final UnmodifiableTransFormula liveTf, final ManagedScript managedScript) {
		final Set<TermVariable> auxVars = new HashSet<>(liveTf.getAuxVars());
		if (auxVars.isEmpty()) {
			return liveTf;
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(liveTf.getInVars(), liveTf.getOutVars(), false,
				liveTf.getNonTheoryConsts(), false, liveTf.getBranchEncoders(), false);
		final Term eliminated = TransFormulaUtils.tryAuxVarEliminationLight(services, managedScript,
				liveTf.getFormula(), auxVars);
		tfb.setFormula(eliminated);
		tfb.setInfeasibility(liveTf.isInfeasible());
		tfb.addAuxVarsButRenameToFreshCopies(auxVars, managedScript);
		return tfb.finishConstruction(managedScript);
	}

	private static <LOC extends IcfgLocation> void initializeMapAndWorklist(final IIcfg<LOC> icfg,
			final ArrayDeque<IcfgEdge> worklist, final HashRelation<IcfgLocation, IProgramVar> result) {
		// outParams are added to exit node via the return transition
		for (final Entry<String, Map<DebugIdentifier, LOC>> procToPps : icfg.getProgramPoints().entrySet()) {
			for (final Entry<DebugIdentifier, LOC> entry : procToPps.getValue().entrySet()) {
				final LOC pp = entry.getValue();
				for (final IcfgEdge outgoing : pp.getOutgoingEdges()) {
					final Set<IProgramVar> inVars = outgoing.getTransformula().getInVars().keySet();
					result.addAllPairs(pp, inVars);
				}
				for (final IcfgEdge incoming : pp.getIncomingEdges()) {
					worklist.add(incoming);
				}
			}
		}
	}

	private static <LOC extends IcfgLocation> void doFixpointIteration(final IIcfg<LOC> icfg,
			final ArrayDeque<IcfgEdge> worklist, final HashRelation<IcfgLocation, IProgramVar> result) {
		while (!worklist.isEmpty()) {
			final IcfgEdge edge = worklist.removeFirst();
			final IcfgLocation src = edge.getSource();
			final IcfgLocation target = edge.getTarget();
			final Set<IProgramVar> liveAfterwards = result.getImage(target);
			final boolean wasModified;
			if ((edge instanceof IIcfgInternalTransition) || (edge instanceof IIcfgSummaryTransition)) {
				// TODO: more precise for summary: do not add vars that are written by return
				wasModified = result.addAllPairs(src,
						DataStructureUtils.difference(liveAfterwards, edge.getTransformula().getOutVars().keySet()));
			} else if ((edge instanceof IIcfgCallTransition) || (edge instanceof IIcfgReturnTransition)) {
				boolean newVarAdded = false;
				for (final IProgramVar pv : liveAfterwards) {
					if (pv.isGlobal()) {
						newVarAdded |= result.addPair(src, pv);
					}
				}
				wasModified = newVarAdded;
			} else {
				throw new AssertionError("Unsupported kind of edge " + edge.getClass().getSimpleName());
			}
			if (wasModified) {
				for (final IcfgEdge incoming : src.getIncomingEdges()) {
					worklist.add(incoming);
				}
			}
		}
	}

}
