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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class TermcompProofBenchmark implements ICsvProviderProvider<Double> {
	private final IUltimateServiceProvider mServices;

	private final TreeMap<Integer, String> mModuleFinite = new TreeMap<>();
	private final TreeMap<Integer, String> mModuleBuchi = new TreeMap<>();
	/**
	 * Is there a remainder module? A remainder module contains remaining traces if decomposition into modules failed.
	 * Null if yet unknown.
	 */
	private Boolean mHasRemainderModule;
	private boolean mRemainderModuleNonterminationKnown;

	public TermcompProofBenchmark(final IUltimateServiceProvider services) {
		mServices = services;
	}

	void reportFiniteModule(final Integer iteration, final INwaOutgoingLetterAndTransitionProvider<?, IPredicate> automaton) {
		final String stringRepresentation = (new AutomatonDefinitionPrinter<>(new AutomataLibraryServices(mServices),
				"finiteAutomatonIteration" + iteration, Format.ATS, automaton)).getDefinitionAsString();
		mModuleFinite.put(iteration, stringRepresentation);
	}

	void reportBuchiModule(final Integer iteration, final INwaOutgoingLetterAndTransitionProvider<?, IPredicate> automaton) {
		final String stringRepresentation = (new AutomatonDefinitionPrinter<>(new AutomataLibraryServices(mServices),
				"buchiAutomatonIteration" + iteration, Format.ATS, automaton)).getDefinitionAsString();
		mModuleBuchi.put(iteration, stringRepresentation);
	}

	void reportRemainderModule(final boolean nonterminationKnown) {
		assert mHasRemainderModule == null : "remainder module already reported";
		mHasRemainderModule = true;
		mRemainderModuleNonterminationKnown = nonterminationKnown;
	}

	void reportNoRemainderModule() {
		assert mHasRemainderModule == null : "remainder module already reported";
		mHasRemainderModule = false;
	}

	@Override
	public String toString() {
		if (mHasRemainderModule == null) {
			return "Decomposition not yet finished";
		}
		if (mHasRemainderModule) {
			if (mRemainderModuleNonterminationKnown) {
				return "Program is not terminating, hence no termination proof";
			}
			return "Unable to prove termination";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("Your program was decomposed into the following automata ");
		sb.append(System.lineSeparator());
		for (final Entry<Integer, String> entry : mModuleFinite.entrySet()) {
			sb.append(entry.getValue());
			sb.append(System.lineSeparator());
		}
		for (final Entry<Integer, String> entry : mModuleBuchi.entrySet()) {
			sb.append(entry.getValue());
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

	@Override
	public ICsvProvider<Double> createCsvProvider() {
		final ICsvProvider<Double> rtr = new SimpleCsvProvider<>(new ArrayList<String>());

		return rtr;
	}

}
