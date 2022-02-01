/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Map.Entry;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class BuchiAutomizerModuleDecompositionBenchmark implements ICsvProviderProvider<String> {

	private final TreeMap<Integer, Integer> mModuleSizeTrivial = new TreeMap<Integer, Integer>();
	private final TreeMap<Integer, Integer> mModuleSizeDeterministic = new TreeMap<Integer, Integer>();
	private final TreeMap<Integer, Integer> mModuleSizeNondeterministic = new TreeMap<Integer, Integer>();
	private final TreeMap<Integer, String> mRankingFunction = new TreeMap<Integer, String>();
	/**
	 * Is there a remainder module? A remainder module contains remaining traces if decomposition into modules failed.
	 * Null if yet unknown.
	 */
	private Boolean mHasRemainderModule;
	private int mRemainderModuleLocations;
	private boolean mRemainderModuleNonterminationKnown;
	private final IBacktranslationService mBacktranslationService;

	public BuchiAutomizerModuleDecompositionBenchmark(final IBacktranslationService service) {
		mBacktranslationService = service;
	}

	void reportTrivialModule(final Integer iteration, final Integer size) {
		mModuleSizeTrivial.put(iteration, size);
	}

	void reportDeterminsticModule(final Integer iteration, final Integer size) {
		mModuleSizeDeterministic.put(iteration, size);
	}

	void reportNonDeterminsticModule(final Integer iteration, final Integer size) {
		mModuleSizeNondeterministic.put(iteration, size);
	}

	void reportRankingFunction(final Integer iteration, final TerminationArgumentResult<IIcfgElement, Term> tar) {
		mRankingFunction.put(iteration, prettyPrintRankingFunction(tar));
	}

	void reportRemainderModule(final int numberLocations, final boolean nonterminationKnown) {
		assert mHasRemainderModule == null : "remainder module already reported";
		mHasRemainderModule = true;
		mRemainderModuleLocations = numberLocations;
		mRemainderModuleNonterminationKnown = nonterminationKnown;
	}

	void reportNoRemainderModule() {
		assert mHasRemainderModule == null : "remainder module already reported";
		mHasRemainderModule = false;
	}

	private String prettyPrintRankingFunction(final TerminationArgumentResult<IIcfgElement, Term> tar) {
		return tar.getRankingFunctionDescription() + " ranking function " + ResultUtil
				.translateExpressionToString(mBacktranslationService, Term.class, tar.getRankingFunction());
	}

	@Override
	public String toString() {
		if (mHasRemainderModule == null) {
			return "Decomposition not yet finished";
		}
		final int modules = mModuleSizeTrivial.size() + mModuleSizeDeterministic.size()
				+ mModuleSizeNondeterministic.size();
		if (modules == 0) {
			if (mHasRemainderModule) {
				if (mRemainderModuleNonterminationKnown) {
					return "Trivial decomposition into one nonterminating module.";
				} else {
					return "Trivial decomposition into one module whose termination is unknown.";
				}
			} else {
				return "Trivial decomposition. There is no loop in your program.";
			}
		}
		int maxNumberOfStatesOfModuleWithTrivialRankingFunction = 0;
		final StringBuilder sb = new StringBuilder();
		sb.append("Your program was decomposed into ");
		sb.append(modules);
		sb.append(" terminating modules ");
		sb.append("(");
		sb.append(mModuleSizeTrivial.size());
		sb.append(" trivial, ");
		sb.append(mModuleSizeDeterministic.size());
		sb.append(" deterministic, ");
		sb.append(mModuleSizeNondeterministic.size());
		sb.append(" nondeterministic)");
		if (mHasRemainderModule) {
			if (mRemainderModuleNonterminationKnown) {
				sb.append(" and one nonterminating remainder module.");
			} else {
				sb.append(" and one module whose termination is unknown.");
			}
		} else {
			sb.append(". ");
		}
		for (final Entry<Integer, Integer> entry : mModuleSizeDeterministic.entrySet()) {
			sb.append("One deterministic module has ");
			sb.append(mRankingFunction.get(entry.getKey()));
			sb.append(" and consists of ");
			sb.append(entry.getValue());
			sb.append(" locations. ");
		}
		for (final Entry<Integer, Integer> entry : mModuleSizeNondeterministic.entrySet()) {
			sb.append("One nondeterministic module has ");
			sb.append(mRankingFunction.get(entry.getKey()));
			sb.append(" and consists of ");
			sb.append(entry.getValue());
			sb.append(" locations. ");
		}
		for (final Entry<Integer, Integer> entry : mModuleSizeTrivial.entrySet()) {
			if (entry.getValue() > maxNumberOfStatesOfModuleWithTrivialRankingFunction) {
				maxNumberOfStatesOfModuleWithTrivialRankingFunction = entry.getValue();
			}
		}
		if (!mModuleSizeTrivial.isEmpty()) {
			sb.append(mModuleSizeTrivial.size());
			sb.append(" modules have a trivial ranking function, the largest among these consists of ");
			sb.append(maxNumberOfStatesOfModuleWithTrivialRankingFunction);
			sb.append(" locations.");
		}
		if (mHasRemainderModule) {
			sb.append(" The remainder module has ");
			sb.append(mRemainderModuleLocations);
			sb.append(" locations.");
		}
		return sb.toString();
	}

	@Override
	public ICsvProvider<String> createCsvProvider() {

		final ArrayList<String> header = new ArrayList<String>();
		header.add("Modules");
		header.add("Trivial modules");
		header.add("Deterministic modules");
		header.add("Nondeterministic modules");
		header.add("Remainer module");
		header.add("Min Locs trivial modules");
		header.add("Avg Locs trivial modules");
		header.add("Max Locs trivial modules");
		header.add("Min Locs deterministic modules");
		header.add("Avg Locs deterministic modules");
		header.add("Max Locs deterministic modules");
		header.add("Min Locs nondeterministic modules");
		header.add("Avg Locs nondeterministic modules");
		header.add("Max Locs nondeterministic modules");

		final int modules = mModuleSizeTrivial.size() + mModuleSizeDeterministic.size()
				+ mModuleSizeNondeterministic.size();

		final ArrayList<String> row = new ArrayList<String>();
		row.add(String.valueOf(modules));
		if (modules == 0) {
			row.add(null);
			row.add(null);
			row.add(null);
			if (mHasRemainderModule == null) {
				row.add("Decomposition not yet finished");
			} else if (mHasRemainderModule) {
				if (mRemainderModuleNonterminationKnown) {
					row.add("Nonterminating");
				} else {
					row.add("Unknown");
				}
			} else {
				row.add("No loop");
			}
			row.add(null);
			row.add(null);
			row.add(null);
			row.add(null);
			row.add(null);
			row.add(null);
			row.add(null);
			row.add(null);
			row.add(null);
		} else {
			row.add(String.valueOf(mModuleSizeTrivial.size()));
			row.add(String.valueOf(mModuleSizeDeterministic.size()));
			row.add(String.valueOf(mModuleSizeNondeterministic.size()));
			if (mHasRemainderModule == null) {
				row.add("Decomposition not yet finished");
			} else if (mHasRemainderModule) {
				if (mRemainderModuleNonterminationKnown) {
					row.add("Nonterminating");
				} else {
					row.add("Unknown");
				}
			} else {
				row.add(null);
			}

			final MinAvgMax triv = getMinAvgMax(mModuleSizeTrivial);
			final MinAvgMax determinisic = getMinAvgMax(mModuleSizeDeterministic);
			final MinAvgMax nondet = getMinAvgMax(mModuleSizeNondeterministic);
			row.add(String.valueOf(triv.min));
			row.add(String.valueOf(triv.avg));
			row.add(String.valueOf(triv.max));
			row.add(String.valueOf(determinisic.min));
			row.add(String.valueOf(determinisic.avg));
			row.add(String.valueOf(determinisic.max));
			row.add(String.valueOf(nondet.min));
			row.add(String.valueOf(nondet.avg));
			row.add(String.valueOf(nondet.max));

		}
		final ICsvProvider<String> rtr = new SimpleCsvProvider<>(header);
		rtr.addRow(row);
		return rtr;
	}

	private MinAvgMax getMinAvgMax(final TreeMap<Integer, Integer> map) {
		final MinAvgMax rtr = new MinAvgMax();

		if (map == null || map.entrySet().size() == 0) {
			rtr.min = 0;
			rtr.avg = 0;
			rtr.max = 0;
			return rtr;
		}

		for (final Entry<Integer, Integer> entry : map.entrySet()) {
			final Integer current = entry.getValue();
			if (current < rtr.min) {
				rtr.min = current;
			}
			if (current > rtr.max) {
				rtr.max = current;
			}
			rtr.avg += current;
		}
		rtr.avg = rtr.avg / map.entrySet().size();

		return rtr;
	}

	private class MinAvgMax {
		int min = Integer.MAX_VALUE;
		double avg = 0;
		int max = Integer.MIN_VALUE;
	}

}
