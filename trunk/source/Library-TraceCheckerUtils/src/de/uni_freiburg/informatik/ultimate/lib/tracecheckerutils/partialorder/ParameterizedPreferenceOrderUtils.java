/*
 * Copyright (C) 2022 Marcel Ebbinghaus
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * An utilization class for Parameterized Preference Orders
 * 
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 * 		The type of Icfg transitions
 */
public class ParameterizedPreferenceOrderUtils<L extends IIcfgTransition<?>> {
	private Set<IProgramVar> mEffectiveGlobalVars;
	private final List<Integer> mMaxSteps;
	private final List<String> mThreadList;
	private final IIcfg<?> mIcfg;
	private HashMap<String, Set<IProgramVar>> mSharedVarsMapReversed;

	ParameterizedPreferenceOrderUtils(final IIcfg<?> icfg, final String threads, final int maxStep,
			final boolean heuristicEnabled) {
		mIcfg = icfg;
		final List<String> allThreads = new ArrayList<>();
		allThreads.addAll(IcfgUtils.getAllThreadInstances(icfg).stream().sorted().collect(Collectors.toList()));
		final String start = "ULTIMATE.start";
		for (int i = allThreads.indexOf(start); i > 0; i--) {
			allThreads.set(i, allThreads.get(i - 1));
		}
		allThreads.set(0, start);

		computeEffectiveGlobalVars(allThreads);

		String[] pairList;
		if (heuristicEnabled) {
			final PreferenceOrderHeuristic<L> heuristic = new PreferenceOrderHeuristic<>(icfg, allThreads,
					mEffectiveGlobalVars, mSharedVarsMapReversed, icfg.getCfgSmtToolkit().getManagedScript());
			heuristic.computeParameterizedOrder();
			
			pairList = heuristic.getParameterizedOrderSequence().split("\\s+");
		} else {
			pairList = threads.split("\\s+");
		}

		List<Integer> maxSteps = new ArrayList<>();
		final List<String> threadList = new ArrayList<>();
		if ("X".equals(pairList[0])) {
			threadList.addAll(allThreads);
			maxSteps = Collections.nCopies(threadList.size(), maxStep);
		} else {
			final List<Boolean> allThreadsBool = new ArrayList<>();
			allThreadsBool.addAll(Collections.nCopies(allThreads.size(), false));
			for (final String pair : pairList) {
				final String[] splittedPair = pair.split(",");
				final Integer index = Integer.parseInt(splittedPair[0]);
				if (allThreads.size() > index) {
					threadList.add(allThreads.get(index));
					maxSteps.add(Integer.parseInt(splittedPair[1]));
					if (!allThreadsBool.get(index)) {
						allThreadsBool.set(index, true);
					}
				}
			}
			for (int i = 0; i < allThreadsBool.size(); i++) {
				if (!allThreadsBool.get(i)) {
					threadList.add(allThreads.get(i));
					maxSteps.add(1);
				}
			}
		}
		mMaxSteps = maxSteps;
		mThreadList = threadList;
	}

	private void computeEffectiveGlobalVars(final List<String> allThreads) {
		// get all global Variables, then iterate over the cfg and mark variables if a procedure accesses it
		final Set<IProgramVar> allProgramVars = IcfgUtils.collectAllProgramVars(mIcfg.getCfgSmtToolkit());
		final HashMap<IProgramVar, Set<String>> sharedVarsMap = new HashMap<>();
		for (final IProgramVar var : allProgramVars) {
			sharedVarsMap.put(var, new HashSet<String>());
		}
		final IcfgEdgeIterator iterator = new IcfgEdgeIterator(mIcfg);
		while (iterator.hasNext()) {
			final IcfgEdge current = iterator.next();
			final String currentProcedure = current.getPrecedingProcedure();
			// only mark with procedures different from "ULTIMATE.start"
			if (!"ULTIMATE.start".equals(currentProcedure)) {
				final Set<IProgramVar> currentVars = new HashSet<>();
				currentVars.addAll(current.getTransformula().getInVars().keySet());
				currentVars.addAll(current.getTransformula().getOutVars().keySet());
				for (final IProgramVar var : currentVars) {
					if (!sharedVarsMap.get(var).contains(currentProcedure)) {
						final Set<String> procedures = sharedVarsMap.get(var);
						procedures.add(currentProcedure);
						sharedVarsMap.put(var, procedures);
					}
				}
			}

		}

		final HashMap<String, Set<IProgramVar>> sharedVarsMapReversed = new HashMap<>();
		for (final String procedure : allThreads) {
			sharedVarsMapReversed.put(procedure, new HashSet<>());
		}

		final Set<IProgramVar> effectiveGlobalVars = new HashSet<>();
		for (final IProgramVar var : sharedVarsMap.keySet()) {
			if (sharedVarsMap.get(var).size() > 1) {
				effectiveGlobalVars.add(var);
				for (final String procedure : sharedVarsMap.get(var)) {
					final Set<IProgramVar> vars = sharedVarsMapReversed.get(procedure);
					if (vars != null) {
						vars.add(var);
						sharedVarsMapReversed.put(procedure, vars);
					}
				}
			}
		}
		mEffectiveGlobalVars = effectiveGlobalVars;
		mSharedVarsMapReversed = sharedVarsMapReversed;
	}

	public Set<IProgramVar> getEffectiveGlobalVars() {
		return mEffectiveGlobalVars;
	}

	public List<Integer> getMaxSteps() {
		return mMaxSteps;
	}

	public List<String> getThreadList() {
		return mThreadList;
	}
}
