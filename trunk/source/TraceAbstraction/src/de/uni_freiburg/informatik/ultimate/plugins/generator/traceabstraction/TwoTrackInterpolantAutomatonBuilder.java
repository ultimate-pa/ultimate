package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class TwoTrackInterpolantAutomatonBuilder {
	
	
	public TwoTrackInterpolantAutomatonBuilder(
			NestedWord<CodeBlock> trace,
			IPredicate precondition,
			IPredicate postcondition,
			IPredicate[] interpolantsSp,
			IPredicate[] interpolantsWp) {
		
	}

}
