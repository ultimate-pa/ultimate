package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

public class OwickiGriesAnnotation<LETTER, PLACE> {

	// Petri net
	private final IPetriNet<LETTER, PLACE> mPetriNet;

	//
	private final Map<PLACE, IPredicate> mFormulaMapping;
	// ...

	public OwickiGriesAnnotation() {
		mPetriNet = null;
		mFormulaMapping = null;
	}

	public int getSize() {
		// ...
		return 0;
	}

	public static <LETTER, PLACE> OwickiGriesAnnotation<LETTER, PLACE> fromFloydHoare(IPetriNet<LETTER, PLACE> net,
			Map<Marking<LETTER, PLACE>, IPredicate> floydHoare, IPredicateUnifier unifier) {
		// ...
		return new OwickiGriesAnnotation<>();
	}

}
