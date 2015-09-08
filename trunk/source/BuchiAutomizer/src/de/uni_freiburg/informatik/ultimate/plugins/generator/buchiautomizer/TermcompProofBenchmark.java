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

import java.util.Map.Entry;
import java.util.ArrayList;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class TermcompProofBenchmark implements ICsvProviderProvider<Double> {
	private final IUltimateServiceProvider m_Services;

	private final TreeMap<Integer, String> m_ModuleFinite = new TreeMap<Integer, String>();
	private final TreeMap<Integer, String> m_ModuleBuchi = new TreeMap<Integer, String>();
	/**
	 * Is there a remainder module? A remainder module contains remaining traces
	 * if decomposition into modules failed. Null if yet unknown.
	 */
	private Boolean m_HasRemainderModule;
	private boolean m_RemainderModuleNonterminationKnown;

	public TermcompProofBenchmark(IUltimateServiceProvider services) {
		m_Services = services;
	}

	void reportFiniteModule(Integer iteration, INestedWordAutomatonSimple<CodeBlock, IPredicate> automaton) {
		String stringRepresentation = (new AtsDefinitionPrinter<>(m_Services, "finiteAutomatonIteration" + iteration, automaton))
				.getDefinitionAsString();
		m_ModuleFinite.put(iteration, stringRepresentation);
	}

	void reportBuchiModule(Integer iteration, INestedWordAutomatonSimple<CodeBlock, IPredicate> automaton) {
		String stringRepresentation = (new AtsDefinitionPrinter<>(m_Services, "buchiAutomatonIteration" + iteration, automaton))
				.getDefinitionAsString();
		m_ModuleBuchi.put(iteration, stringRepresentation);
	}

	void reportRemainderModule(boolean nonterminationKnown) {
		assert m_HasRemainderModule == null : "remainder module already reported";
		m_HasRemainderModule = true;
		m_RemainderModuleNonterminationKnown = nonterminationKnown;
	}

	void reportNoRemainderModule() {
		assert m_HasRemainderModule == null : "remainder module already reported";
		m_HasRemainderModule = false;
	}

	@Override
	public String toString() {
		if (m_HasRemainderModule == null) {
			return "Decomposition not yet finished";
		}
		if (m_HasRemainderModule) {
			if (m_RemainderModuleNonterminationKnown) {
				return "Program is not terminating, hence no termination proof";
			} else {
				return "Unable to prove termination";
			}
		} else {
			StringBuilder sb = new StringBuilder();
			sb.append("Your program was decomposed into the following automata ");
			sb.append(System.lineSeparator());
			for (Entry<Integer, String> entry : m_ModuleFinite.entrySet()) {
				sb.append(entry.getValue());
				sb.append(System.lineSeparator());
			}
			for (Entry<Integer, String> entry : m_ModuleBuchi.entrySet()) {
				sb.append(entry.getValue());
				sb.append(System.lineSeparator());
			}
			return sb.toString();
		}
	}

	@Override
	public ICsvProvider<Double> createCvsProvider() {
		ICsvProvider<Double> rtr = new SimpleCsvProvider<>(new ArrayList<String>());

		return rtr;
	}

}
