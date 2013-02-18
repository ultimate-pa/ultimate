package local.stalin.smt.theory.linar;

import java.util.LinkedList;
import java.util.Map;

import local.stalin.logic.Term;
import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.DPLLEngine;
import local.stalin.smt.dpll.Literal;

import org.apache.log4j.Logger;

/**
 * Class used to decide formulae over linear arithmetic over integers. This
 * class uses the {@link LinArSolve} class as base to solve LP relaxations of
 * all integer constraints. Then, it combines Gomory cut generation algorithms
 * with branch-and-bound to check satisfiability.
 * 
 * @author Juergen Christ
 */
public class IntLinArSolve extends LinArSolve {
	
	// List of all integer variables
	LinkedList<LinVar> miv;
	LinkedList<Literal> cuts = new LinkedList<Literal>();
	
	// Statistics
	int numcuts;
	int numbranches;
	long cutgentime;
	/**
	 * Construct a new integer arithmetic solver. Tableau simplification is
	 * prevented since it is not sound for integers.
	 * @param engine DPLL engine this solver is for.
	 */
	public IntLinArSolve(DPLLEngine engine) {
		super(engine);
		miv = new LinkedList<LinVar>();
		numcuts = 0;
		numbranches = 0;
		cutgentime = 0;
		// Prevent tableau simplification since this is not sound on integers
		doSimplifyTableau = false;
	}
	/**
	 * Add a non-basic variable. This variable is assumed to be integer-valued.
	 * @param name Name of the variable in SMTLIB format.
	 * @return Variable corresponding to <code>name</code>.
	 */
	public LinVar addVar(Term name,boolean isint) {
		assert isint;
		LinVar res = super.addVar(name, isint);
		miv.push(res);
		return res;
	}
	@Override
	public Clause computeConflictClause() {
		Clause c = check(); 
//		assert(checkClause(c));
//		System.err.println("computeConflictClause returns " + c);
		return c;
	}
	/**
	 * Check whether a clause contains a literal.
	 * @param c   Clause to search <code>lit</code> in.
	 * @param lit Literal to search.
	 * @return <code>true</code> iff <code>lit</code> is in <code>c</code>.
	 */
	@SuppressWarnings("unused")
	private boolean clausecontains(Clause c,Literal lit) {
		for( int i = 0; i < c.getSize(); ++i )
			if( c.getLiteral(i) == lit )
				return true;
		return false;
	}
	private void branch(LinVar v) {
//		assert(miv.contains(v));
//		assert(!v.mcurval.ma.isIntegral());
		System.err.println("Branching on " + v + " = " + v.mcurval);
		BoundConstraint bc = new BoundConstraint(v.mcurval.floor(), v);
		++numbranches;
//		if( numbranches % 100 == 0 )
//			System.err.println(System.nanoTime() + ": numbranches: " + numbranches);
		mengine.addAtom(bc);
	}

	@Override
	public Clause checkpoint() {
		Clause c = super.check();
		if( c == null ) {
//			for( LinVar iv : miv ) {
//				if( !iv.mcurval.ma.isIntegral() ) {
//					CutSupportSet css = cutPossible(iv);
//					if( css != null && css.unsat() ) {
//						Logger.getRootLogger().info("Unsatifiable cut");
//						return css.interpolateUnsatCut(mengine.getSMTTheory(), mengine.getFormulaCount()-1);
//					}
//				}
//			}
//			searchPropagations();
		}
		return c;
	}
	
	@Override
	protected Clause check() {
		Clause c = super.check();
		if (c != null)
			return c;
		
//				assert(checkPreCutGen());
		// Satisfiable in the reals
		assert(moob.isEmpty());
		for (LinVar iv : miv) {
			if (!iv.mcurval.ma.isIntegral()) {
				// found non-integer value for integer variable
				// We prefer cuts over branches
				CutSupportSet css = cutPossible(iv);
				if (css != null) {
					if( css.unsat() ) {
						Logger.getRootLogger().info("Unsatisfiable cut");
						return css.interpolateUnsatCut
							(mengine.getSMTTheory(), mengine.getFormulaCount()-1);
					}
					++numcuts;
//							if( numcuts % 100 == 0 )
//								System.err.println(System.nanoTime() + ": numcuts: " + numcuts);
					long starttime = System.nanoTime();
					MutableAffinTerm cut = css.computeCut();
					Rational normFactor = cut.getGCD().inverse();
					Literal lit = generateConstraint(cut,false);
					if (lit.getAtom().getDecideStatus() == lit.negate())
						// Conflict: Cut is already propositionally violated
						return css.computeCutClause(mengine.getSMTTheory(), lit, normFactor, mengine.getFormulaCount()-1);
					mproplist.add(lit);
					BoundConstraint bc = (BoundConstraint) lit.getAtom();
					bc.cutexpl = css.computeCutClause(mengine.getSMTTheory(), lit, normFactor, mengine.getFormulaCount()-1);
					cutgentime += System.nanoTime() - starttime;
				} else {
					branch(iv);
				}
			}// no else case since we do not branch-and-bound here...
		}
		return null;
	}
	@Override
	public void printStatistics(Logger logger) {
		super.printStatistics(logger);
		logger.info("Number of cuts: " + numcuts);
		logger.info("Time for cut-generation: " + cutgentime);
		logger.info("Number of branchings: " + numbranches);
	}
	
	/**
	 * Checks whether a cut can be generated for <code>iv</code>.
	 * @param iv Integer variable not having integral value.
	 * @return Set of all literals needed for this cut or 
	 * 			<code>null</code> if cut is not possible.
	 */
	private CutSupportSet cutPossible(LinVar iv) {
		if( !iv.mbasic )
			return null;
		for (MatrixEntry entry = iv.headEntry.nextInRow;
			 entry != iv.headEntry; entry = entry.nextInRow) {
			LinVar nb = entry.column;
			if (!entry.coeff.isIntegral()
				&& !nb.mcurval.equals(nb.mubound)
				&& !nb.mcurval.equals(nb.mlbound))
				return null;
		}
			
		CutSupportSet res = new CutSupportSet(iv.mcurval.ma.frac());
		for (MatrixEntry entry = iv.headEntry.nextInRow;
			 entry != iv.headEntry; entry = entry.nextInRow) {
			LinVar nb = entry.column;
			assert nb.misint;
			Rational coeff = entry.coeff;
			if (coeff.isIntegral())
				continue;
			if (nb.mlbound.equals(nb.mubound))
				res.addFixedVar(nb, coeff);
			else
				res.addIneq(nb, coeff, nb.mcurval.equals(nb.mubound));
		}
		return res;
	}
	
	/**
	 * Generate a bound constraint for a given variable. We use
	 * {@link IntBoundConstraint}s to represent bounds for integer variables
	 * and linear combination thereof. Those constraints are optimized to
	 * prevent strict bounds by manipulating the bounds. That way, we convert
	 * strict bounds in the reals into non-strict bounds in the integers. Note
	 * however that bounds returned here need not be integral. They only do not
	 * have a non-zero coefficient in front of the infinitesimal parameter.
	 * @param var      Variable to set bound on.
	 * @param bound    Bound to set on <code>var</code>.
	 * @param fac      Factor originally in front of var.
	 *                 This is used to restore the SMT formula and to 
	 *                 determine if <= or >= should be generated.
	 * @param strict   Is the bound strict?
	 * @return Constraint representing this bound.
	 */
	@Override
	protected Literal generateConstraint(LinVar var, Rational bound, boolean isLowerBound, boolean strict) {
		Rational rbound = bound.floor();
		if ((strict ^ isLowerBound) && bound.isIntegral()) {
			rbound = rbound.sub(Rational.ONE);
		}
		InfinitNumber infBound = new InfinitNumber(rbound, Rational.ZERO);
		BoundConstraint bc = var.mconstraints.get(infBound);
		if (bc != null) {
			return isLowerBound ? bc.negate() : bc;
		}
		bc = new BoundConstraint(infBound, var);
//		assert(checkCoeffChain(bc.mvar));
		mengine.addAtom(bc);
		return isLowerBound ? bc.negate() : bc;
	}
	// -- Assertion Stuff --
	@SuppressWarnings("unused")
	private boolean checkClause(Clause c) {
		if( c != null ) {
			for( int i = 0; i < c.getSize(); ++i ) {
				Literal lit = c.getLiteral(i);
				BoundConstraint bc = (BoundConstraint)lit.getAtom();
				if( bc.getDecideStatus() != lit.negate() ) {
					System.err.println("Constraint with wrong decision status in conflict clause");
					return false;
				}
			}
		}
		return true;
	}
	@SuppressWarnings("unused")
	private boolean checkPreCutGen() {
		if( !checkConsistency() )
			return false;
		if( !checkvals() )
			return false;
		for( LinVar v : mbasics ) {
			if( v.outOfBounds() ) {
				System.err.println(v + " still out of bounds after check!");
				return false;
			}
			if( !checkCoeffChain(v) )
				return false;
		}
		for( LinVar v : mnonbasics ) {
			if( v.outOfBounds() ) {
				System.err.println(v + " still out of bounds after check!");
				return false;
			}
			if( !checkCoeffChain(v) )
				return false;
		}
		return true;
	}
	@SuppressWarnings("unused")
	private boolean checkATle0(AffinTerm at) {
		MutableInfinitNumber val = new MutableInfinitNumber(at.constant,Rational.ZERO);
		for( Map.Entry<LinVar,Rational> me : at.factors.entrySet() ) {
			val.addmul(me.getKey().mcurval,me.getValue());
		}
//		System.err.println("checkATle0: val = " + val);
		if( val.compareTo(new MutableInfinitNumber(Rational.ZERO,Rational.ZERO)) <= 0 ) {
			System.err.println("at <= 0! Value is " + val);
			return false;
		}
		return true;
	}
	// Checks whether a literal is NOT satisfied in the current setting.
	@SuppressWarnings("unused")
	private boolean checkLiteralUnsat(Literal lit) {
		BoundConstraint bc = (BoundConstraint)lit.getAtom();
		LinVar var = bc.getVar();
		if( lit.getSign() == 1 ) {
			if( bc.getBound().compareTo(bc.mvar.mubound) >= 0 )
				System.err.println("Constraint not sharper!");
			return var.mcurval.compareTo(bc.getBound()) > 0;
		}
		if( bc.getInverseBound().compareTo(bc.mvar.mlbound) <= 0 )
			System.err.println("Constraint not sharper!");
		return var.mcurval.compareTo(bc.getInverseBound()) < 0;
	}
	@Override
	public void dumpModel(Logger logger) {
		for (LinVar v : miv) {
			if (v.mcurval.ma.isIntegral())
				System.err.println("Integer value for " + v);
			else
				System.err.println("Non-Integer value for " + v);
		}
		super.dumpModel(logger);
	}
	
}
