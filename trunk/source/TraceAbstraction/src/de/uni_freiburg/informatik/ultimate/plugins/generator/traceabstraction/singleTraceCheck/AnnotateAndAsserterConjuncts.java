package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class AnnotateAndAsserterConjuncts extends AnnotateAndAsserter {

	public AnnotateAndAsserterConjuncts(SmtManager smtManager,
			NestedSsa nestedSSA, Word<CodeBlock> trace) {
		super(smtManager, nestedSSA, trace);
	}

}
