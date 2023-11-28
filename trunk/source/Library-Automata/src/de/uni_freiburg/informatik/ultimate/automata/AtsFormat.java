/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.IFormat;
import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.alternating.visualization.AlternatingAutomatonWriter;
import de.uni_freiburg.informatik.ultimate.automata.counting.CaWriter;
import de.uni_freiburg.informatik.ultimate.automata.counting.CountingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.CaDatastructureWriter;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.CountingAutomatonDataStructure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.INwaAtsFormatter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaWriter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessWriterToString;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.IPetriAtsFormatter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.NetWriter;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.visualization.TreeAutomatonWriter;
import de.uni_freiburg.informatik.ultimate.automata.tree.visualization.TreeAutomatonWriterUniqueId;

/**
 * Defines how different kinds of automata are printed in the "automata script" (ATS) format.
 *
 * @see AutomatonDefinitionPrinter.Format.ATS
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class AtsFormat implements IFormat {
	@Override
	public String getFileEnding() {
		return "ats";
	}

	@Override
	public void printHeader(final PrintWriter pw, final String header) {
		pw.println(AutomatonDefinitionPrinter.generateDefaultAtsHeader(header));
	}

	@Override
	public <L, S> void printNestedWordAutomaton(final PrintWriter printWriter, final String name,
			final INestedWordAutomaton<L, S> nwa) {
		new NwaWriter<>(printWriter, name, nwa, getNwaFormatter());
	}

	protected <L, S> INwaAtsFormatter<L, S> getNwaFormatter() {
		return new INwaAtsFormatter.ToString<>();
	}

	@Override
	public <L, S> void printCountingAutomaton(final PrintWriter printWriter, final String name,
			final CountingAutomaton<L, S> automaton) {
		new CaWriter<>(printWriter, name, automaton);
	}

	@Override
	public <L, S> void printTreeAutomaton(final PrintWriter printWriter, final String name,
			final TreeAutomatonBU<? extends IRankedLetter, S> automaton) {
		new TreeAutomatonWriter<>(printWriter, name, automaton);
	}

	@Override
	public <L, S> void printCountingAutomatonDataStructure(final PrintWriter printWriter, final String name,
			final CountingAutomatonDataStructure<L, S> automaton) {
		new CaDatastructureWriter<>(printWriter, name, automaton);
	}

	@Override
	public <L, S> void printPetriNet(final PrintWriter printWriter, final String name,
			final BoundedPetriNet<L, S> net) {
		new NetWriter<>(printWriter, name, net, getPetriFormatter());
	}

	protected <L, S> IPetriAtsFormatter<L, S> getPetriFormatter() {
		return new IPetriAtsFormatter.ToString<>();
	}

	@Override
	public <L, S> void printAlternatingAutomaton(final PrintWriter printWriter, final String name,
			final AlternatingAutomaton<L, S> alternating) {
		new AlternatingAutomatonWriter<>(printWriter, name, alternating);
	}

	@Override
	public <L, S> void printBranchingProcess(final PrintWriter printWriter, final String name,
			final BranchingProcess<L, S> branchingProcess) {
		new BranchingProcessWriterToString<>(printWriter, name, branchingProcess);
	}

	static class AtsNumerateFormat extends AtsFormat {
		@Override
		protected <L, S> INwaAtsFormatter<L, S> getNwaFormatter() {
			return new INwaAtsFormatter.UniqueId<>();
		}

		@Override
		public <L, S> void printCountingAutomaton(final PrintWriter printWriter, final String name,
				final CountingAutomaton<L, S> automaton) {
			AutomatonDefinitionPrinter.failUnsupported();
		}

		@Override
		public <L, S> void printTreeAutomaton(final PrintWriter printWriter, final String name,
				final TreeAutomatonBU<? extends IRankedLetter, S> automaton) {
			new TreeAutomatonWriterUniqueId<>(printWriter, name, automaton);
		}

		@Override
		public <L, S> void printCountingAutomatonDataStructure(final PrintWriter printWriter, final String name,
				final CountingAutomatonDataStructure<L, S> automaton) {
			AutomatonDefinitionPrinter.failUnsupported();
		}

		@Override
		protected <L, S> IPetriAtsFormatter<L, S> getPetriFormatter() {
			return new IPetriAtsFormatter.UniqueId<>();
		}

		@Override
		public <L, S> void printAlternatingAutomaton(final PrintWriter printWriter, final String name,
				final AlternatingAutomaton<L, S> alternating) {
			AutomatonDefinitionPrinter.failUnsupported();
		}

		@Override
		public <L, S> void printBranchingProcess(final PrintWriter printWriter, final String name,
				final BranchingProcess<L, S> branchingProcess) {
			AutomatonDefinitionPrinter.failUnsupported();
		}
	}

	static class AtsQuotedFormat extends AtsFormat {
		@Override
		protected <L, S> INwaAtsFormatter<L, S> getNwaFormatter() {
			return new INwaAtsFormatter.ToStringWithHash<>();
		}

		@Override
		public <L, S> void printCountingAutomaton(final PrintWriter printWriter, final String name,
				final CountingAutomaton<L, S> automaton) {
			AutomatonDefinitionPrinter.failUnsupported();
		}

		@Override
		public <L, S> void printTreeAutomaton(final PrintWriter printWriter, final String name,
				final TreeAutomatonBU<? extends IRankedLetter, S> automaton) {
			AutomatonDefinitionPrinter.failUnsupported();
		}

		@Override
		public <L, S> void printCountingAutomatonDataStructure(final PrintWriter printWriter, final String name,
				final CountingAutomatonDataStructure<L, S> automaton) {
			AutomatonDefinitionPrinter.failUnsupported();
		}

		@Override
		protected <L, S> IPetriAtsFormatter<L, S> getPetriFormatter() {
			return new IPetriAtsFormatter.ToStringWithUniqueNumber<>();
		}

		@Override
		public <L, S> void printAlternatingAutomaton(final PrintWriter printWriter, final String name,
				final AlternatingAutomaton<L, S> alternating) {
			AutomatonDefinitionPrinter.failUnsupported();
		}

		@Override
		public <L, S> void printBranchingProcess(final PrintWriter printWriter, final String name,
				final BranchingProcess<L, S> branchingProcess) {
			AutomatonDefinitionPrinter.failUnsupported();
		}
	}
}