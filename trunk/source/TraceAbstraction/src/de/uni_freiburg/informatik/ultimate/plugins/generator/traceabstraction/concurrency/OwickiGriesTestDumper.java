/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AtsFormat;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.NamedAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.INwaAtsFormatter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.IPetriAtsFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class OwickiGriesTestDumper<L extends IAction> {
	private final Map<L, String> mAlphabetNames = new HashMap<>();
	private final ManagedScript mMgdScript;

	public OwickiGriesTestDumper(final IUltimateServiceProvider services, final TaskIdentifier ident,
			final IIcfg<?> icfg, final IPetriNet<L, IPredicate> initialNet,
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> proofAutomata) {
		mMgdScript = icfg.getCfgSmtToolkit().getManagedScript();

		final String variablesComment = getVariablesComment(icfg);
		final String alphabetComments = getAlphabetDefinition(initialNet, proofAutomata);

		final var automata = new ArrayList<NamedAutomaton<L, IPredicate>>();
		automata.add(new NamedAutomaton<>("program", initialNet));

		int i = 1;
		for (final var proofAut : proofAutomata) {
			automata.add(new NamedAutomaton<>("proof" + i, proofAut));
			i++;
		}

		writeAutomataToFile(services, ident.toString(), variablesComment + System.lineSeparator() + alphabetComments,
				automata.toArray(NamedAutomaton[]::new));
	}

	private String getVariablesComment(final IIcfg<?> icfg) {
		final var symbolTable = icfg.getCfgSmtToolkit().getSymbolTable();

		final var actualVars = Stream.concat(symbolTable.getGlobals().stream(),
				icfg.getCfgSmtToolkit().getProcedures().stream().flatMap(p -> symbolTable.getLocals(p).stream()))
				.map(IProgramVar::getTermVariable);
		final var constVars = symbolTable.getConstants().stream()
				.map(c -> mMgdScript.variable(c.getDefaultConstant().getFunction().getName(), c.getSort()));

		return "//@ variables " + Stream.concat(actualVars, constVars)
				.map(tv -> "(" + PrintTerm.quoteIdentifier(tv.getName()) + " " + tv.getSort() + ")")
				.collect(Collectors.joining(" "));
	}

	private String getAlphabetDefinition(final IPetriNet<L, ?> program,
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> proofAutomata) {
		final var alphabet = Stream
				.concat(program.getAlphabet().stream(),
						proofAutomata.stream().flatMap(nwa -> nwa.getAlphabet().stream()))
				.distinct().collect(Collectors.toList());

		final var alphabetDefinition = new StringBuilder();
		int counter = 1;
		for (final L letter : alphabet) {
			final String name = "[" + counter + "]";
			counter++;
			mAlphabetNames.put(letter, name);

			alphabetDefinition.append("//@ semantics ");
			alphabetDefinition.append(name);
			alphabetDefinition.append(" ");
			alphabetDefinition.append(getTransFormulaDescription(letter.getTransformula()));
			alphabetDefinition.append(System.lineSeparator());
		}
		return alphabetDefinition.toString();
	}

	private String getTransFormulaDescription(final UnmodifiableTransFormula transformula) {
		final var assignedVars = transformula.getAssignedVars().stream().map(pv -> pv.getTermVariable().getName())
				.collect(Collectors.joining(",", "{", "}"));

		final Map<TermVariable, Term> substitution = new HashMap<>();
		for (final var entry : transformula.getOutVars().entrySet()) {
			substitution.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		for (final var entry : transformula.getInVars().entrySet()) {
			TermVariable subst;
			if (!transformula.getAssignedVars().contains(entry.getKey())) {
				subst = entry.getKey().getTermVariable();
			} else if (entry.getKey() instanceof IProgramNonOldVar) {
				subst = ((IProgramNonOldVar) entry.getKey()).getOldVar().getTermVariable();
			} else {
				final String name = "old(" + entry.getKey().getTermVariable().getName() + ")";
				subst = mMgdScript.variable(name, entry.getKey().getSort());
			}
			substitution.put(entry.getValue(), subst);
		}
		final Term newFormula = PureSubstitution.apply(mMgdScript, substitution, transformula.getFormula());
		return assignedVars + " " + newFormula.toString();
	}

	private void writeAutomataToFile(final IUltimateServiceProvider services, final String filename,
			final String atsCommands, final NamedAutomaton<L, IPredicate>... automata) {
		services.getLoggingService().getLogger(getClass())
				.info("Dumping Owicki-Gries test to " + Paths.get(filename).toAbsolutePath().toString());
		AutomatonDefinitionPrinter.writeAutomatonToFile(new AutomataLibraryServices(services), filename,
				new CustomFormat(), "", atsCommands, automata);
	}

	private <LETTER> Map<LETTER, String> getAlphabetMap(final Collection<LETTER> alphabet) {
		return alphabet.stream().collect(Collectors.toMap(Function.identity(), x -> quote(mAlphabetNames.get(x))));
	}

	private static String quote(final String str) {
		return "\"" + str + "\"";
	}

	private class CustomFormat extends AtsFormat {
		@Override
		protected <LETTER, STATE> INwaAtsFormatter<LETTER, STATE> getNwaFormatter() {
			return new ProofAutomatonFormatter<>();
		}

		@Override
		protected <LETTER, PLACE> IPetriAtsFormatter<LETTER, PLACE> getPetriFormatter() {
			return new PetriProgramFormatter<>();
		}
	}

	private class ProofAutomatonFormatter<LETTER, STATE> implements INwaAtsFormatter<LETTER, STATE> {
		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol) {
			return getAlphabetMap(alphabet);
		}

		@Override
		public Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			final var result = new HashMap<STATE, String>();
			for (final STATE state : states) {
				result.put(state, quote(((IPredicate) state).getFormula().toString()));
			}
			return result;
		}

	}

	private class PetriProgramFormatter<LETTER, PLACE> implements IPetriAtsFormatter<LETTER, PLACE> {
		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			return getAlphabetMap(alphabet);
		}

		@Override
		public Map<PLACE, String> getPlacesMapping(final Collection<PLACE> places) {
			final var result = new HashMap<PLACE, String>();
			int counter = 0;
			for (final PLACE place : places) {
				result.put(place, "l" + counter);
				counter++;
			}
			return result;
		}
	}
}
