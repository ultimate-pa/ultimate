package de.uni_freiburg.informatik.ultimate.graphvr;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class Converter {

	public static TraceAbstractionProtos.NestedWordAutomaton fromAutomaton(
			NestedWordAutomaton<CodeBlock, IPredicate> automaton) {
		return null;
	}

	public static TraceAbstractionProtos.Alphabet fromAlphabet(Set<CodeBlock> alphabet) {
		return null;
	}

	public static TraceAbstractionProtos.CodeBlock fromCodeblock(CodeBlock codeblock) {
		return null;
	}

	public static TraceAbstractionProtos.Predicate fromPredicate(IPredicate predicate) {
		return null;
	}

	public static TraceAbstractionProtos.TAPreferences fromTAPreferences(TAPreferences preferences) {
		return null;
	}

	public static TraceAbstractionProtos.Result fromResult(AbstractCegarLoop.Result result) {
		return null;
	}

	private static TraceAbstractionProtos.NestedWordAutomaton.transition fromTransition(
			Map<IPredicate, Map<CodeBlock, Set<IPredicate>>> transition) {
		return null;
	}
	
	
	private static TraceAbstractionProtos.StateSet fromStateSet(Set<IPredicate> stateset) {
		return null;
	}
}