package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;

public final class BranchingProcessWriterToString<LETTER, STATE> extends BranchingProcessWriter<LETTER, STATE>
{
	public BranchingProcessWriterToString(final PrintWriter writer,
		final String name, final BranchingProcess<LETTER, STATE> branchingProcess) {
		super(writer, name, branchingProcess);
	}

	@Override
	protected Map<LETTER, String> getAlphabetMapping(Collection<LETTER> alphabet) {
		final Map<LETTER, String> alphabetMapping = new HashMap<>();
		for (final LETTER letter : alphabet) {
			alphabetMapping.put(letter, quoteAndReplaceBackslashes(letter));
		}
		return alphabetMapping;
	}

	@Override
	protected Map<Condition<LETTER, STATE>, String> getConditionsMapping(Collection<Condition<LETTER, STATE>> conditions) {
		final HashMap<Condition<LETTER, STATE>, String> ConditionsMapping = new HashMap<>();
		for (final Condition<LETTER, STATE> condition : conditions) {
			ConditionsMapping.put(condition, quoteAndReplaceBackslashes(condition));
		}
		return ConditionsMapping;
	}
	
}
