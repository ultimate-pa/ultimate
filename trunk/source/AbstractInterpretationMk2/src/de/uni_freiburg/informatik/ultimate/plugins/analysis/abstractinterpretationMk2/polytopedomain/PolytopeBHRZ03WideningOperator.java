package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import org.apache.log4j.Logger;

import parma_polyhedra_library.NNC_Polyhedron;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractWideningOperator;

/**
 * The same as the normal widening but using the BHRZ03_widening_assign instead
 * 
 * @author GROSS-JAN
 *
 */
public class PolytopeBHRZ03WideningOperator implements
		IAbstractMergeOperator<PolytopeState>,
		IAbstractWideningOperator<PolytopeState> {
	private static final String s_operatorID = "BHRZ03_WIDENING";
	private final Logger mLogger;

	private final PolytopeDomain mDomain;

	public PolytopeBHRZ03WideningOperator(Logger logger, PolytopeDomain domain) {
		mLogger = logger;
		mDomain = domain;
	}

	@Override
	public IAbstractState<PolytopeState> apply(IAbstractState<PolytopeState> a,
			IAbstractState<PolytopeState> b) {
		PolytopeState result = b.getConcrete().copy();

		result.synchroniseDimensions(a.getConcrete());

		// mLogger.debug("Widening Polytopes (before): \n" + a.toString() +
		// "\n -- and -- \n" + b.toString() + "\n -- result -- \n" +
		// result.toString());

		// widen the polytope of the result state (copy of b) by the polytope of
		// a
		// since the argument-polytope must be contained in the other one
		NNC_Polyhedron pRes = result.getConcrete().getPolytope();
		NNC_Polyhedron pA = a.getConcrete().getPolytope();
		pRes.upper_bound_assign(pA);
		pRes.BHRZ03_widening_assign(pA, null);
		// pA.widening_assign(pRes, null);

		// mLogger.debug("Widening Polytopes: \n" + a.toString() +
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
