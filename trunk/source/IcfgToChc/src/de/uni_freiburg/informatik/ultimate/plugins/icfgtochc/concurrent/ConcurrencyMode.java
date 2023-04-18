/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public enum ConcurrencyMode {
	/**
	 * A single instance of the main thread is started initially. More threads are created dynamically through fork and
	 * join statements.
	 */
	SINGLE_MAIN_THREAD,

	/**
	 * An unbounded number of threads (all with the same template) are all started at the same time.
	 */
	PARAMETRIC;

	/**
	 * Given an {@link IIcfg}, determines how many thread instances of each template should be considered, and for which
	 * thread templates we assume an unbounded number of instances.
	 *
	 * @param icfg
	 *            The (unpetrified) control flow graph of the concurrent program
	 * @param level
	 *            The thread modularity level of the analysis
	 * @return a pair, where the first component maps each thread template to the number of instances to consider, and
	 *         the second component contains all threads that may have more than {@code level} instances.
	 */
	public Pair<Map<String, Integer>, List<String>> getThreadNumbersAndUnboundedThreads(final IIcfg<IcfgLocation> icfg,
			final int level) {
		if (this == ConcurrencyMode.PARAMETRIC) {
			final var numberOfThreads =
					icfg.getInitialNodes().stream().collect(Collectors.toMap(loc -> loc.getProcedure(), loc -> level));
			final var unbounded = List.copyOf(numberOfThreads.keySet());
			return new Pair<>(numberOfThreads, unbounded);
		}

		assert this == ConcurrencyMode.SINGLE_MAIN_THREAD : "Unknown mode: " + this;

		final var forksInLoops = IcfgUtils.getForksInLoop(icfg);
		final var instanceMap = icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap();
		final Map<String, Integer> numberOfThreads = new HashMap<>();
		icfg.getInitialNodes().forEach(x -> numberOfThreads.put(x.getProcedure(), 1));
		final List<String> unboundedThreads = new ArrayList<>();
		// TODO: This needs to be more accurate in general
		for (final var fork : instanceMap.keySet()) {
			final String procedure = fork.getNameOfForkedProcedure();
			// TODO: Only add if fork is reachable
			if (forksInLoops.contains(fork)) {
				numberOfThreads.put(procedure, level);
				unboundedThreads.add(procedure);
			} else {
				final Integer oldCount = numberOfThreads.getOrDefault(procedure, 0);
				if (oldCount == level) {
					unboundedThreads.add(procedure);
				} else {
					numberOfThreads.put(procedure, oldCount + 1);
				}
			}
		}

		return new Pair<>(numberOfThreads, unboundedThreads);
	}

	/**
	 * Determines the initial locations of a given program.
	 *
	 * @param icfg
	 *            The control flow graph of the program
	 * @param instances
	 *            The set of thread instances considered by the analyis
	 * @return A mapping from initially running thread instances to their initial locations
	 */
	public Map<ThreadInstance, IcfgLocation> getInitialLocations(final IIcfg<IcfgLocation> icfg,
			final List<ThreadInstance> instances) {
		switch (this) {
		case PARAMETRIC:
			// combine each initial location (usually there is only one) with ALL instances of its template
			return icfg
					.getInitialNodes().stream().flatMap(l -> instances.stream()
							.filter(i -> i.getTemplateName().equals(l.getProcedure())).map(i -> new Pair<>(i, l)))
					.collect(Collectors.toMap(Pair::getKey, Pair::getValue));
		case SINGLE_MAIN_THREAD:
			// combine each initial location (usually there is only one) with instance 0 of its template
			return icfg.getInitialNodes().stream()
					.collect(Collectors.toMap(l -> new ThreadInstance(l.getProcedure(), 0), l -> l));
		}
		throw new UnsupportedOperationException("Unknown mode: " + this);
	}
}