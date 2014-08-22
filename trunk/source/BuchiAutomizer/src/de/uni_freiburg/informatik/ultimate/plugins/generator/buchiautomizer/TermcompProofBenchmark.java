package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Map.Entry;
import java.util.ArrayList;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class TermcompProofBenchmark implements ICsvProviderProvider<Double> {

	private final TreeMap<Integer, String> m_ModuleFinite = new TreeMap<Integer, String>();
	private final TreeMap<Integer, String> m_ModuleBuchi = new TreeMap<Integer, String>();
	/**
	 * Is there a remainder module? A remainder module contains remaining traces
	 * if decomposition into modules failed. Null if yet unknown.
	 */
	private Boolean m_HasRemainderModule;
	private boolean m_RemainderModuleNonterminationKnown;

	public TermcompProofBenchmark() {
	}

	void reportFiniteModule(Integer iteration, INestedWordAutomatonSimple<CodeBlock, IPredicate> automaton) {
		String stringRepresentation = (new AtsDefinitionPrinter<>("finiteAutomatonIteration" + iteration, automaton))
				.getDefinitionAsString();
		m_ModuleFinite.put(iteration, stringRepresentation);
	}

	void reportBuchiModule(Integer iteration, INestedWordAutomatonSimple<CodeBlock, IPredicate> automaton) {
		String stringRepresentation = (new AtsDefinitionPrinter<>("buchiAutomatonIteration" + iteration, automaton))
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
