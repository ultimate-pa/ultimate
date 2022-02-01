package de.uni_freiburg.informatik.ultimate.automata.tree.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;

public class TreeAutomatonWriterUniqueId<LETTER extends IRankedLetter, STATE>
		extends TreeAutomatonWriter<LETTER, STATE> {

	public TreeAutomatonWriterUniqueId(final PrintWriter writer, final String name,
			final TreeAutomatonBU<LETTER, STATE> automaton) {
		super(writer, name, automaton, "");
	}

	@Override
	protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
		int counter = 0;
		final Map<LETTER, String> alphabetMapping = new LinkedHashMap<>();
		for (final LETTER letter : alphabet) {
			alphabetMapping.put(letter, 'l' + Integer.toString(counter));
			counter++;
		}
		return alphabetMapping;
	}

	@Override
	protected Map<STATE, String> getStateMapping(final Collection<STATE> states) {
		int counter = 0;
		final Map<STATE, String> stateMapping = new LinkedHashMap<>();
		for (final STATE state : states) {
			stateMapping.put(state, 'q' + Integer.toString(counter));
			counter++;
		}
		return stateMapping;
	}
}
