package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

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

	public static <LETTER, PLACE> OwickiGriesAnnotation<LETTER, PLACE> fromFloydHoare(IUltimateServiceProvider services,
			CfgSmtToolkit csToolkit, IPetriNet<LETTER, PLACE> net, Map<Marking<LETTER, PLACE>, IPredicate> floydHoare) {
		final BasicPredicateFactory factory = new BasicPredicateFactory(services, csToolkit.getManagedScript(),
				csToolkit.getSymbolTable());

		// TODO Use factory.and(preds)
		// ...

		return new OwickiGriesAnnotation<>();
	}

}
