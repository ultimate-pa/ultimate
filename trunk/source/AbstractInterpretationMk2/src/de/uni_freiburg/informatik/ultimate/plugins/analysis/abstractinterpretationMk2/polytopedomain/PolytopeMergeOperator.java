package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import org.apache.log4j.Logger;

import parma_polyhedra_library.NNC_Polyhedron;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractWideningOperator;

public class PolytopeMergeOperator implements
		IAbstractMergeOperator<PolytopeState>,
		IAbstractWideningOperator<PolytopeState> {
	private static final String s_operatorID = "POLYTOPE_UPPER_BOUND";

	private final Logger mLogger;

	private final PolytopeDomain mDomain;

	public PolytopeMergeOperator(Logger logger, PolytopeDomain domain) {
		mLogger = logger;
		mDomain = domain;
	}

	@Override
	public IAbstractState<PolytopeState> apply(IAbstractState<PolytopeState> a,
			IAbstractState<PolytopeState> b) {
		PolytopeState result = a.getConcrete().copy();

		result.synchroniseDimensions(b.getConcrete());

		// merge the polytope into the result state
		NNC_Polyhedron pRes = result.getConcrete().getPolytope();
		pRes.upper_bound_assign(b.getConcrete().getPolytope());

		// mLogger.debug("Merging Polytopes: \n" + a.toString() +
		// "\n -- and -- \n" + b.toString() + "\n -- result -- \n" +
		// result.toString());

		assert (pRes.contains(a.getConcrete().getPolytope()));
		assert (pRes.contains(b.getConcrete().getPolytope()));

		result.updateDimensions();

		return (IAbstractState<PolytopeState>) result;
	}

	public static String getOperatorID() {
		return s_operatorID;
	}

	@Override
	public String toString() {
		return s_operatorID;
	}
}
