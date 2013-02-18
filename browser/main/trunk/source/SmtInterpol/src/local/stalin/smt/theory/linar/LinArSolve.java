package local.stalin.smt.theory.linar;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map.Entry;

import local.stalin.logic.FormulaVariable;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.DPLLAtom;
import local.stalin.smt.dpll.DPLLEngine;
import local.stalin.smt.dpll.InterpolationInfo;
import local.stalin.smt.dpll.Interpolator;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.dpll.Theory;
import local.stalin.smt.theory.cclosure.CCMixedLiteralInterpolator;
import local.stalin.smt.theory.cclosure.EqualityAtom;

import org.apache.log4j.Logger;

/**
 * Class implementing a decision procedure for linear arithmetic over 
 * rationals. An algorithm proposed by Dutertre and de Moura is used. This 
 * class can easily be extended to reason about linear arithmetic over 
 * integers. It provides tableau simplification, theory propagation, conflict 
 * set generation and interpolation.
 * 
 * To build a tableau, we create slack variables for every linear combination
 * of non-basic variables. To be able to recognize recurring linear
 * combinations, we canonicalize every linear combination and remember them the
 * first time we see them. Canonicalization takes advantage of the ordering of
 * non-basic variables. We transform every linear combination to an equivalent
 * one with a coefficient of 1 in front of the first non-basic variable.
 * 
 * Theory propagation comes in two flavors: bound propagation and bound
 * refinement propagation. 
 * 
 * With bound propagation, we propagate every bound <code>x <= c'</code> after
 * setting bound <code>x <= c</code> where <code>c<=c'</code>. Lower bounds are
 * handled the same way.
 * 
 * With bound refinement propagation, we propagate all bounds that are outside
 * the possible range. If it is possible to derive an upper or lower bound of a
 * basic variable from the bound of the corresponding linear combination of all
 * non-basic variables, we propagate all bounds bigger than the derived upper
 * resp. smaller than the derived lower bound.
 * 
 * @author Juergen Christ
 */
public class LinArSolve implements Theory {
	// RTTI for toArray-calls
	final static Literal[] EMPTY_LITS_ARRAY = new Literal[0];
	final static Rational[] EMPTY_RATIONAL_ARRAY = new Rational[0];
	/**
	 *  Should tableau simplification be performed. Note that this flag is 
	 *  currently only used in {@link #setLiteral(Literal)}. Integer solvers
	 *  should set it to false <strong>before</strong> the first call to 
	 *  setLiteral since tableau simplification is not sound for integers!
	 */
	protected boolean doSimplifyTableau;
	
	DPLLEngine mengine;
	// TODO: Check whether we need these lists
	ArrayList<LinVar> mbasics;
	ArrayList<LinVar> mnonbasics;
	// All Literals to propagate
	Queue<Literal> mproplist;
	// Save all normalized linear combinations
	HashMap<Map<LinVar,Rational>,LinVar> mterms;
	// List of all variables outside their bounds.
	// I prefer a tree set here since it provides ordering, retrieval of the 
	// first element, addition of elements and uniqueness of elements!
	TreeSet<LinVar> moob;
	// List of all variables removed by simplifying operations
	// TODO: Check if we are interested in a complete model or not
	//       If not, then we can safely remove this list!
	ArrayList<LinVar> msimps;
	// Set of currently basic variables
	HashSet<LinVar> mcurbasics;
	
	/// --- Statistics variables ---
	// Pivot counter
	int numpivots;
	// Time needed for pivoting operations
	long pivottime;
	// Time needed to calculate bound refinement propagations
	long boundrefinementtime;
	// Number of successful bound refinement propagations
	int numboundrefinement;
	// Number of bound refinement searches
	int numboundrefinementsearch;
	
	/**
	 * Basic initialization.
	 * @param engine DPLLEngine this theory is used in.
	 */
	public LinArSolve(DPLLEngine engine) {
		mengine = engine;
		mbasics = new ArrayList<LinVar>();
		mnonbasics = new ArrayList<LinVar>();
		mproplist = new ArrayDeque<Literal>();
		mterms = new HashMap<Map<LinVar,Rational>,LinVar>();
		moob = new TreeSet<LinVar>();
		mcurbasics = new HashSet<LinVar>();
		numpivots = 0;
		pivottime = 0;
		boundrefinementtime = 0;
		numboundrefinement = 0;
		numboundrefinementsearch = 0;
		doSimplifyTableau = true;
	}
	
	/// --- Introduction of variables ---
	/**
	 * Add a new non-basic variable.
	 * @param name  Name of the variable
	 * @param isint Is the variable integer valued
	 * @return Newly created variable
	 */
	public LinVar addVar(Term name,boolean isint) {
		LinVar var = new LinVar(name, isint);
		mnonbasics.add(var);
		return var;
	}
	
	public LinVar generateLinVar(Map<LinVar, Rational> factors) {
		if( factors.size() == 1 ) {
			Map.Entry<LinVar,Rational> me = factors.entrySet().iterator().next();
			LinVar var = me.getKey();
			return var;
		}
		LinVar var = mterms.get(factors);
		// Term not known
		if( var == null ) {
			var = new LinVar(new LinTerm(factors));
			var.misint = this instanceof IntLinArSolve;
			mterms.put(factors, var);
			mbasics.add(var);
			mcurbasics.add(var);
		}
		//assert(checkBRPCounters());
		return var;
	}
	
	/**
	 * Generate a constraint from an affine term. 
	 * The generated constraint is <code> at <(=) 0</code>.
	 * @param at     Affine Term to create a constraint for.
	 * @param strict Is the bound strict?
	 * @return Newly created literal.
	 */
	public Literal generateConstraint(AffinTerm at,boolean strict) {
		return generateConstraint(new MutableAffinTerm(at.isIntegral()).add(Rational.ONE, at), 
								  strict);
	}
	/**
	 * Generate a bound constraint for <code>at <(=) 0</code>. If 
	 * <code>online</code> is <code>true</code>, the value for this constraint
	 * is calculated while creation.
	 * @param at     Affine input term (may be unit term c_i*x_i+c or 
	 * 				 sum_i c_i*x_i+c)
	 * @param strict   Strict bound (< instead of <=)
	 * @param online   Should value for this term be calculated?
	 * @param remember Should the variable remember the generated constraint?
	 * @return
	 */
	public Literal generateConstraint(MutableAffinTerm at,boolean strict) {
		Rational normFactor = at.getGCD().inverse();
		at.mul(normFactor);
		LinVar var = generateLinVar(at.summands);
		if (at.getFirstFormulaNr() > at.getLastFormulaNr()) {
			/* variable is mixed */
			if (var.mixedVar == null) {
				local.stalin.logic.Theory theory = mengine.getSMTTheory();
				Sort sort = theory.getSort("Int");
				TermVariable mixedVar = theory.createFreshTermVariable("la", sort);
				LinVar mixedLinVar = new LinVar(theory.term(mixedVar), true);
				var.mixedVar = mixedLinVar;
			}
		}

		return generateConstraint(var, at.constant.ma.negate(), normFactor.isNegative(), strict);
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		DPLLAtom atom = literal.getAtom();
		if( !(atom instanceof BoundConstraint) )
			return;
//		assert(checkoobcontent());
//		System.err.println("Backtracking " + literal);
		BoundConstraint bc = (BoundConstraint)atom;
//		assert( !bc.mvar.outOfBounds() || (moob.contains(bc.mvar) && bc.mvar.mbasic) );
		// Distinguish between propagated and decided literals 
		if( bc.oldbound != null ) {
			assert(bc.oldassert != null || bc.oldbound.isInfinity());
			assert(bc.oldassert == null || !bc.oldbound.isInfinity());
			// Here, I do not change the value of the variable. Only its bounds and constraints are changed back
			if( literal.getSign() == 1 ) {
				assert(bc.mvar.upperassert == literal);
				bc.mvar.mubound = bc.oldbound;
				bc.mvar.upperassert = bc.oldassert;
			} else {
				assert(bc.mvar.lowerassert == literal);
				bc.mvar.mlbound = bc.oldbound;
				bc.mvar.lowerassert = bc.oldassert;
			}
			// might have to remove this variable from possible brps
			if (bc.oldassert == null && !bc.mvar.mbasic) {
				for (MatrixEntry entry = bc.mvar.headEntry.nextInCol;
					entry != bc.mvar.headEntry; entry = entry.nextInCol) {
					if( entry.coeff.isNegative() ^ literal.getSign() < 0 )
						++entry.row.numlower;
					else
						++entry.row.numupper;
				}
			}
			bc.oldbound = null;
		}
		bc.oldassert = null;
		assert(checkoobcontent());
		assert( !bc.mvar.outOfBounds() || (moob.contains(bc.mvar) && bc.mvar.mbasic) );
		while( !mproplist.isEmpty() ) {
			Literal lit = mproplist.remove();
			BoundConstraint bl = (BoundConstraint)lit.getAtom();
			if( bl.mpropexpl != null ) {
				// Clear all caches
				bl.mpropexpl = null;
				bl.mpropexplcoeffs = null;
			}
		}
		assert(checkvarbound(bc.getVar()));
		assert(checkBRPCounters());
	}

	@Override
	public Clause computeConflictClause() {
		Clause c = check();
//		assert(checkBRPCounters());
//		searchPropagations();
		return c;
	}

	@Override
	public Clause getConflictClause() {
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		while( !mproplist.isEmpty() ) {
			Literal lit = mproplist.remove();
//			System.err.println("Propagating " + lit + (((BoundConstraint)lit.getAtom()).mpropexpl == null ? " [BP]" : " [BRP]"));
			if (lit.getAtom().getDecideStatus() == null)
				return lit;
		}
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		BoundConstraint bc = (BoundConstraint)literal.getAtom();
//		System.err.print("getUnitClause: " + bc);
		LinVar var = bc.getVar();
		if (bc.cutexpl != null) {
			Clause res = bc.cutexpl;
			bc.cutexpl = null;
			return res;
		}
		if( bc.mpropexpl != null ) {
//			System.err.println(" [BRP]");
			// Bound refinement propagation
			assert(checkbrpcs(bc));
			Clause res = interpolateBoundRefinement(bc);
			bc.mpropexpl = null;
			bc.mpropexplcoeffs = null;
			return res;
		}
//		System.err.println(" [BP]");
		if( literal.getSign() > 0 ) {
//			System.err.println("getUnitClause: Constraint: " + literal + "; upper bound: " + var.mubound);
			assert(bc.impliedByUpperBound(var.mubound));
			// Bound constraint propagation
			return interpolateBound(literal.negate(),bc.mvar.upperassert);
		}
		assert(bc.impliedByLowerBound(var.mlbound));
		// Bound constraint propagation
		return interpolateBound(bc.mvar.lowerassert,literal.negate());
	}

	@Override
	public Clause setLiteral(Literal literal) {
		if( doSimplifyTableau )
			simplifyTableau();
		DPLLAtom atom = literal.getAtom();
		if( !(atom instanceof BoundConstraint) )
			return null;
		assert(checkBRPCounters());
//		assert(checkConsistency());
//		if( atom instanceof CutConstraint )
//			System.err.println("Asserting cut");
//		Logger.getRootLogger().debug(literal);
//		assert(checkoobcontent());
//		System.err.println("setLiteral: " + literal);
		BoundConstraint bc = (BoundConstraint)atom;
		assert(bc.oldassert == null);
		assert(bc.oldbound == null);
		LinVar var = bc.mvar;
		if( literal.getSign() == 1 ) {
//			Logger.getRootLogger().debug("Setting upper bound " + bc.getBound() + " on variable " + bc.mvar.toString() + (bc.mvar.mbasic ? " [basic]" : " [nonbasic]"));
//			dumpModel(Logger.getRootLogger());
			// upper bound asserting
			if( bc.getBound().less(var.mlbound) )
				return interpolateBound(var.lowerassert,literal);
			if( var.mubound.lesseq(bc.getBound()) )
				return null;
			bc.oldbound = var.mubound;
			bc.oldassert = var.upperassert;
			assert(bc.oldassert != null || bc.oldbound.isInfinity());
			assert(bc.oldassert == null || !bc.oldbound.isInfinity());
			boolean newubound = var.upperassert == null;
			var.mubound = bc.getBound();
			var.upperassert = literal;
			if (!var.mbasic)
				var.update(this, var.mubound, moob, newubound, false);
			else if (var.mcurval.compareTo(var.mubound) > 0)
				moob.add(var);
//			System.err.println("Asserted: " + literal);
			// Prevent double propagation
			Entry<InfinitNumber,BoundConstraint> nextbc = 
				var.mconstraints.higherEntry(bc.getBound());
			while (nextbc != null && nextbc.getValue().getDecideStatus() == null) {
				nextbc.getValue().cutexpl = null;
				nextbc.getValue().mpropexpl = null;
				nextbc.getValue().mpropexplcoeffs = null;
				mproplist.add(nextbc.getValue());
				nextbc = var.mconstraints.higherEntry(nextbc.getKey());
			}
//			assert(checkvarbound(var));
//			assert(checkvals());
//			assert(checkoobcontent());
//			assert(checkCoeffChain(var));
//			assert(checkConsistency());
			assert(checkBRPCounters());
			return fixOobs();
		}
		InfinitNumber lb = bc.getInverseBound();
//		Logger.getRootLogger().debug("Setting lower bound " + lb + " on variable " + bc.mvar.toString() + (bc.mvar.mbasic ? " [basic]" : " [nonbasic]"));
//		dumpModel(Logger.getRootLogger());
		if( var.mubound.less(lb) )
			return interpolateBound(literal,var.upperassert);
		if( lb.lesseq(var.mlbound) )
			return null;
		bc.oldbound = var.mlbound;
		bc.oldassert = var.lowerassert;
		assert(bc.oldassert != null || bc.oldbound.isInfinity());
		assert(bc.oldassert == null || !bc.oldbound.isInfinity());
		boolean newlbound = var.lowerassert == null;
		var.mlbound = lb;
		var.lowerassert = literal;
		if (!var.mbasic)
			var.update(this, lb, moob, false, newlbound);
		else if (var.mcurval.compareTo(lb) < 0)
			moob.add(var);
		Entry<InfinitNumber, BoundConstraint> nextbc = 
			var.mconstraints.lowerEntry(bc.getBound());
		while (nextbc != null && nextbc.getValue().getDecideStatus() == null) {
			nextbc.getValue().cutexpl = null;
			nextbc.getValue().mpropexpl = null;
			nextbc.getValue().mpropexplcoeffs = null;
			mproplist.add(nextbc.getValue().negate());
			nextbc = var.mconstraints.lowerEntry(nextbc.getKey());
		}
//		assert(checkvarbound(var));
//		assert(checkvals());
//		assert(checkoobcontent());
//		assert(checkCoeffChain(var));
//		assert(checkConsistency());
		assert(checkBRPCounters());
		return fixOobs();
	}

	@Override
	public Clause checkpoint() {
		Clause c = check();
//		if (c == null)
//			searchPropagations();
//		assert(checkBRPCounters());
		return c;
	}

	@Override
	public void dumpModel(Logger logger) {
		calculateSimpVals();
		logger.info("Assignments:");
//		for( LinVar var : mbasics ) {
//			logger.info(var + " = " + var.mcurval);
//		}
		for( LinVar var : mnonbasics ) {
			logger.info(var + " = " + var.mcurval);
		}
		if( msimps != null ) {
			for( LinVar var : msimps ) {
				logger.info(var + " = " + var.mcurval);
			}
		}
	}

	@Override
	public void printStatistics(Logger logger) {
		logger.info("Number of pivoting-Operations: " + numpivots);
		logger.info("Time for pivoting: " + pivottime);
		logger.info("Time for bound refinement: " + boundrefinementtime);
		logger.info("Number of bound refinement propagations: " + numboundrefinement);
		logger.info("No. of bound refinement searches: " + numboundrefinementsearch);
		logger.info("No. of simplified variables: " + (msimps != null ? msimps.size() : 0));
	}
	
	/**
	 * Pivot basic variable <code>basic</code> and non-basic variable 
	 * <code>nonbasic</code> and update the value of <code>basic</code>.
	 * @param pivotEntry  the entry in the matrix around which we pivot.
	 *              Its row and column are the variables that are swapped.
	 * @param val   Value to set for <code>basic</code>.
	 */
	protected void pivotAndUpdate(MatrixEntry pivotEntry,InfinitNumber val) {
		LinVar basic = pivotEntry.row;
		LinVar nonbasic = pivotEntry.column;
		assert(basic.mbasic);
		assert(!nonbasic.mbasic);
		Rational coeff = pivotEntry.coeff;
		InfinitNumber theta = val.subdiv(basic.mcurval,coeff);
		basic.mcurval = val;
		nonbasic.mcurval = nonbasic.mcurval.add(theta);
		if( nonbasic.outOfBounds() )
			moob.add(nonbasic);
		for (MatrixEntry ptr = nonbasic.headEntry.nextInCol;
			ptr != nonbasic.headEntry; ptr = ptr.nextInCol) {
			if (ptr.row == basic)
				continue;
			LinVar cb = ptr.row;
			cb.mcurval = cb.mcurval.addmul(theta,ptr.coeff);
			if( cb.outOfBounds() )
				moob.add(cb);
		}
		pivot(pivotEntry);
	}
	/**
	 * Pivot nonbasic versus basic variables along a coefficient.
	 * @param coeff Coefficient specifying basic and nonbasic variable.
	 */
	protected final void pivot(MatrixEntry pivotEntry) {
		++numpivots;
		long starttime = System.nanoTime();
		assert checkBRPCounters();
		LinVar basic = pivotEntry.row;
		LinVar nonbasic = pivotEntry.column;
		assert(basic.mbasic);
		assert(!nonbasic.mbasic);
		basic.mbasic = false;
		nonbasic.mbasic = true;
		
		/* swap row/columns */
		MatrixEntry rowStart = basic.headEntry;
		MatrixEntry colStart = nonbasic.headEntry;
		nonbasic.headEntry = rowStart;
		basic.headEntry = colStart;
		rowStart.row = nonbasic;
		colStart.column = basic;
		
		boolean res = mcurbasics.remove(basic);
		assert(res);
		res = mcurbasics.add(nonbasic);
		assert(res);

		pivotEntry.removeFromMatrix();
		MatrixEntry rowptr = colStart.nextInCol;
		/* remove the column from the matrix to avoid getting
		 * confused with newly added elements.
		 */
		colStart.nextInCol = colStart.prevInCol = colStart;

		// basic = X + 1/coeff*nonbasic
		Rational coeff = pivotEntry.coeff.inverse();
		Rational ncoeff = coeff.negate();
		// Equation 2: nonbasic = -coeff*X + coeff*basic
		MatrixEntry entry = rowStart.nextInRow;
		while (entry.column.compareTo(basic) < 0) {
			entry.row = nonbasic;
			entry.coeff = entry.coeff.mul(ncoeff);
			entry = entry.nextInRow;
		}
		entry.row = nonbasic;
		entry.insertBefore(basic, coeff);
		while (entry != rowStart) {
			entry.row = nonbasic;
			entry.coeff = entry.coeff.mul(ncoeff);
			entry = entry.nextInRow;
		}
		// End of equation 2
		
		// Adjust brp numbers
		if( coeff.isNegative() ) {
			nonbasic.numupper = basic.numupper;
			nonbasic.numlower = basic.numlower;
			if( nonbasic.lowerassert == null )
				--nonbasic.numupper;
			if( nonbasic.upperassert == null )
				--nonbasic.numlower;
			if( basic.upperassert == null )
				++nonbasic.numlower;
			if( basic.lowerassert == null )
				++nonbasic.numupper;
		} else {
			nonbasic.numupper = basic.numlower;
			nonbasic.numlower = basic.numupper;
			if( nonbasic.lowerassert == null )
				--nonbasic.numupper;
			if( nonbasic.upperassert == null )
				--nonbasic.numlower;
			if( basic.upperassert == null )
				++nonbasic.numupper;
			if( basic.lowerassert == null )
				++nonbasic.numlower;
		}
		// Substitution
		for (; rowptr != colStart; rowptr = rowptr.nextInCol) {
			LinVar cb = rowptr.row;
			assert(cb.mbasic);
			assert(cb != basic);
			assert(cb != nonbasic);
			
			Rational coeff2 = rowptr.coeff;
			rowptr.removeFromRow();
			if( coeff2.isNegative() ) {
				if( nonbasic.upperassert == null )
					--cb.numlower;
				if( nonbasic.lowerassert == null )
					--cb.numupper;
			} else {
				if( nonbasic.upperassert == null )
					--cb.numupper;
				if( nonbasic.lowerassert == null )
					--cb.numlower;
			}
			// cb = Y + coeff2*nonbasic
			cb.headEntry.add(coeff2, rowStart);
			if (cb.numupper == 0 || cb.numlower == 0)
				propagate(cb);
		}
		assert checkBRPCounters();
		//assert checkMatrixLinks();
		pivottime += System.nanoTime() - starttime;
//		System.err.println("Pivoting took " + (System.nanoTime() - starttime));
		assert(checkBRPCounters());
	}
	
	/**
	 * Check whether all constraints can be satisfied. Here, we use the set of
	 * all variables outside their bounds. Rest of this algorithm is copied 
	 * from original paper.
	 * 
	 * If the formula is satisfiable, we additionally search for bound 
	 * refinement propagations and calculate the values of all variables
	 * simplified out.
	 * @return Conflict clause or <code>null</code> if formula is satisfiable.
	 */
	protected Clause check() {
		return null;
	}
	
	protected Clause fixOobs() {
//		assert(checkoobcontent());
	poll_loop: 
		while (!moob.isEmpty()) {
			LinVar oob = moob.pollFirst();
//			System.err.println("Polling queue: " + oob);
			assert(oob.mbasic || !oob.outOfBounds());
//			assert(checkCoeffChain(oob));
//			assert(checkChain(oob));
//			dumpBasics();
//			assert(oob.mcoeffs instanceof TreeMap);
			if( oob.mcurval.compareTo(oob.mlbound) < 0 ) {
				for (MatrixEntry entry = oob.headEntry.nextInRow;
				     entry != oob.headEntry; entry = entry.nextInRow) {
					if (entry.coeff.isNegative() 
						? entry.column.isDecrementPossible()
						: entry.column.isIncrementPossible()) {
						pivotAndUpdate(entry,oob.mlbound);
//						done = true;
						continue poll_loop;
					}
				}
				moob.add(oob);
				return interpolateUnsat(oob.lowerassert);
			} else if (oob.mcurval.compareTo(oob.mubound) > 0) {
				for (MatrixEntry entry = oob.headEntry.nextInRow;
			     	entry != oob.headEntry; entry = entry.nextInRow) {
					if (entry.coeff.isNegative() 
						? entry.column.isIncrementPossible()
						: entry.column.isDecrementPossible()) {
						pivotAndUpdate(entry, oob.mubound);
//						done = true;
						continue poll_loop;
					}	
				}
				moob.add(oob);
				return interpolateUnsat(oob.upperassert);
			}
		} // end of queue polling
//		dumpBasics();
//		assert(checkoobcontent());
//		assert(checkoob());
//		assert(checkConsistency());
		return null;
	}
	
	/**
	 * Generate an interpolant for a failed assertion of <code>lit</code>.
	 * @param lit Literal that could not be asserted.
	 * @return Conflict clause and interpolant.
	 */
	protected Clause interpolateUnsat(Literal lit) {
		ArrayList<Literal> lits = new ArrayList<Literal>();
		ArrayList<Rational> coeffs = new ArrayList<Rational>();
		lits.add(lit.negate());
		coeffs.add(Rational.ONE);
		BoundConstraint bc = (BoundConstraint)lit.getAtom();
		LinVar var = bc.mvar;
//		assert(var.mbasic);
//		Coefficient c = var.mcoeffs;
		if( lit.getSign() < 0 ) {
//			assert(var.mcurval.compareTo(bc.getInverseBound()) < 0);
			// We could not assert a lower bound
			for (MatrixEntry entry = var.headEntry.nextInRow;
				entry != var.headEntry; entry = entry.nextInRow) {
				Rational val = entry.coeff;
				if( val.isNegative() ) {
//					assert(entry.column.lowerassert != null);
					lits.add(entry.column.lowerassert.negate());
					coeffs.add(val.negate());
				} else {
//					assert(entry.column.upperassert != null);
					lits.add(entry.column.upperassert.negate());
					coeffs.add(val);
				}
			}
		} else {
			for (MatrixEntry entry = var.headEntry.nextInRow;
				entry != var.headEntry; entry = entry.nextInRow) {
				Rational val = entry.coeff;
				if( val.isNegative() ) {
//					assert(entry.column.upperassert != null);
					lits.add(entry.column.upperassert.negate());
					coeffs.add(val.negate());
				} else {
	//				assert(entry.column.lowerassert != null);
					lits.add(entry.column.lowerassert.negate());
					coeffs.add(val);
				}
			}
		}
		return interpolate(lits.toArray(EMPTY_LITS_ARRAY),coeffs.toArray(EMPTY_RATIONAL_ARRAY));
	}
	
	/**
	 * Compute an interpolant for conflicting bounds.
	 * 
	 * This function assumes, that lower AND upper IMPLIES FALSE. Thus, the
	 * conflict clause will be {lower.negate,upper.negate}
	 * @param lower Lower bound
	 * @param upper Upper bound
	 * @return Conflict clause containing interpolant
	 */
	protected Clause interpolateBound(Literal lower,Literal upper) {
		assert(lower != null);
		assert(upper != null);
		return interpolate(new Literal[]{lower.negate(),upper.negate()},new Rational[]{Rational.ONE,Rational.ONE});
	}
	/**
	 * Interpolation and conflict clause generation for a bound refinement
	 * propagation. <code>lit</code> is assumed to be proposed because of a
	 * bound refinement.
	 * @param bc  Atom of this literal
	 * @return Conflict clause and interpolants usable as unit clause.
	 */
	protected Clause interpolateBoundRefinement(BoundConstraint bc) {
		assert(bc.mpropexpl != null && bc.mpropexplcoeffs != null);
		return interpolate(bc.mpropexpl,bc.mpropexplcoeffs);
	}

	/**
	 * Generates Craig Interpolants for a given set of literals. Here, I
	 * normalize all literals to the form <code>0<=t</code>.
	 * @param lits   Conflict clause (not conflict set!!!)
	 * @param coeffs Combination coefficients.
	 * @return Clause containing all interpolants and the conflict clause.
	 */
	@SuppressWarnings("unchecked")
	protected Clause interpolate(Literal[] lits,Rational[] coeffs) {
		assert(lits.length == coeffs.length);
		int numIpls = mengine.getFormulaCount() - 1;
		MutableAffinTerm[] its = new MutableAffinTerm[numIpls];
		Set<BoundConstraint>[] mixedAtoms = new HashSet[numIpls];
		for( int i = 0; i < numIpls; ++i )
			its[i] = new MutableAffinTerm(this instanceof IntLinArSolve);
		for( int i = 0; i < lits.length; ++i ) {
			Literal l = lits[i];
			BoundConstraint bc = (BoundConstraint)l.getAtom();
			/* add positive if literal sign is negative.  This is because
			 * the literal in the conflict clause is negated. 
			 */
			boolean addPositive = lits[i].getSign() == -1;
			for( int j = bc.getLastFormulaNr(); j < numIpls; ++j ) {
				// all lits have to be negated. Thus, if l.getSign() == -1, setting l.negate() leads to a conflict
				// Here, we are in A
				if (j < bc.getFirstFormulaNr()) {
					bc.combineMixedInterpolationTerm(its[j], coeffs[i], addPositive, j);
					if (mixedAtoms[j] == null)
						mixedAtoms[j] = new HashSet<BoundConstraint>();
					mixedAtoms[j].add(bc);
				} else {
					bc.combineInterpolationTerm(its[j], coeffs[i], addPositive);
				}
			}
		}
		InterpolationInfo ipls[] = new InterpolationInfo[numIpls];
		for( int i = 0; i < numIpls; ++i ) {
			local.stalin.logic.Theory theory = mengine.getSMTTheory();
			LinInterpolant term = new LinInterpolant(its[i], mixedAtoms[i]);
			if (mixedAtoms[i] != null) {
				FormulaVariable fvar = 
					theory.createFreshFormulaVariable("LA");
				LinArInterpolator interpolator = new LinArInterpolator(theory, fvar, term);
				HashMap<DPLLAtom,Interpolator> mixedInterpolators = 
					new HashMap<DPLLAtom,Interpolator>();
				for (BoundConstraint bc : mixedAtoms[i]) {
					mixedInterpolators.put(bc, interpolator);
				}
				ipls[i] = new InterpolationInfo(theory.atom(fvar), mixedInterpolators);
			} else {
				Map<DPLLAtom,Interpolator> mixedInterpolators = Collections.emptyMap(); 
				ipls[i] = new InterpolationInfo(
						term.createFormula(theory),
						mixedInterpolators);
			}
		}
		return new Clause(lits,ipls);
	}
	
	protected void propagate(LinVar basic) {
		MutableInfinitNumber lb = new MutableInfinitNumber();
		MutableInfinitNumber ub = new MutableInfinitNumber();
		assert basic.mbasic : "Non-Basic variable currently residing in basic variable set!";
		for (MatrixEntry entry = basic.headEntry.nextInRow;
			entry != basic.headEntry; entry = entry.nextInRow) {
			LinVar nb = entry.column;
			Rational coeff = entry.coeff;
			if (coeff.isNegative()) {
				lb.addmul(nb.mubound, coeff);
				ub.addmul(nb.mlbound, coeff);
			} else {
				ub.addmul(nb.mubound, coeff);
				lb.addmul(nb.mlbound, coeff);
			}
		}
		
		InfinitNumber newlb = lb.toInfinitNumber();
		InfinitNumber newub = ub.toInfinitNumber();
		if (basic.mlbound.compareTo(newlb) < 0)
			propagateLowerBound(basic, newlb);
		if (basic.mubound.compareTo(newub) > 0)
			propagateUpperBound(basic, newub);
	}
	
	protected void propagateLowerBound(LinVar basic, InfinitNumber newlb) {
		Entry<InfinitNumber, BoundConstraint> prop = basic.mconstraints.lowerEntry(newlb); 
		if (prop != null) {
			BoundConstraint propbc = prop.getValue();
			assert(propbc.getBound().compareTo(newlb) < 0);
			if (propbc.getDecideStatus() != null
					|| propbc.mpropexpl != null)
				return; // conflict will be reported soon
			int numcoeffs = 0;
			for (MatrixEntry entry = basic.headEntry.nextInRow;
				entry != basic.headEntry; entry = entry.nextInRow)
				numcoeffs++;
			Rational[] coeffs = new Rational[numcoeffs+1];
			Literal[] lits = new Literal[numcoeffs+1];
			int i = 0;
			for (MatrixEntry entry = basic.headEntry.nextInRow;
				entry != basic.headEntry; entry = entry.nextInRow) {
				LinVar nb = entry.column;
				Rational coeff = entry.coeff;
				coeffs[i] = coeff.abs();
				if (coeff.isNegative()) {
					lits[i] = nb.upperassert.negate();
				} else {
					lits[i] = nb.lowerassert.negate();
				}
				if (lits[i] == null)
					throw new NullPointerException();
				i++;
			}
			coeffs[numcoeffs] = Rational.ONE;
			lits[numcoeffs] = propbc.negate();
			propbc.cutexpl = null;
			propbc.mpropexpl = lits;
			propbc.mpropexplcoeffs = coeffs;
			mproplist.add(propbc.negate());
//			System.err.println("propagate lower: "+nextbc.negate());
		}
	}
	
	protected void propagateUpperBound(LinVar basic, InfinitNumber newub) {
		Entry<InfinitNumber, BoundConstraint> prop = basic.mconstraints.ceilingEntry(newub); 
		if (prop != null) {
			BoundConstraint propbc = prop.getValue();
			assert(propbc.getBound().compareTo(newub) >= 0);
			if (propbc.getDecideStatus() != null
					|| propbc.mpropexpl != null)
				return; // conflict will be reported soon
			int numcoeffs = 0;
			for (MatrixEntry entry = basic.headEntry.nextInRow;
				entry != basic.headEntry; entry = entry.nextInRow)
				numcoeffs++;
			Rational[] coeffs = new Rational[numcoeffs+1];
			Literal[] lits = new Literal[numcoeffs+1];
			int i = 0;
			for (MatrixEntry entry = basic.headEntry.nextInRow;
				entry != basic.headEntry; entry = entry.nextInRow) {
				LinVar nb = entry.column;
				Rational coeff = entry.coeff;
				coeffs[i] = coeff.abs();
				if (coeff.isNegative()) {
					lits[i] = nb.lowerassert.negate();
				} else {
					lits[i] = nb.upperassert.negate();
				}
				if (lits[i] == null)
					throw new NullPointerException();
				i++;
			}
			coeffs[numcoeffs] = Rational.ONE;
			lits[numcoeffs] = propbc;
			propbc.cutexpl = null;
			propbc.mpropexpl = lits;
			propbc.mpropexplcoeffs = coeffs;
			mproplist.add(propbc);
//			System.err.println("propagate upper: "+nextbc);
		}
	}

	/**
	 * Dump the equations for all current basic variables.
	 */
	protected void dumpBasics() {
		for( LinVar v : mbasics ) {
			Logger.getRootLogger().debug(v.headEntry);
		}
		for( LinVar v : mnonbasics ) {
			Logger.getRootLogger().debug(v.headEntry);
		}
		Logger.getRootLogger().debug("End dump!");
	}
	
	/**
	 * Dump the equations of all variables simplified out of the tableau.
	 */
	protected void dumpSimps() {
		if( msimps == null )
			return;
		for( LinVar v : msimps ) {
			Logger.getRootLogger().debug(v.headEntry);
		}
	}
	
	/**
	 * Dump the equation for basic variable <code>var</code>.
	 * @param var Basic variable to dump equations for.
	 */
	protected void dumpTableau(LinVar var) {
		/*assert(var.mbasic);
		Logger.getRootLogger().debug("Begin equation dump:");
		Coefficient coeff = var.mcoeffs;
		String add = "";
		StringBuilder sb = new StringBuilder();
		sb.append(var).append(" = ");
		while( coeff != Coefficient.dummyendcoeff ) {
			sb.append(add);
			sb.append(coeff.coeff);
			sb.append("*(");
			sb.append(coeff.nonbasic);
			sb.append(')');
			add = "+";
			coeff = coeff.nextnonbasic;
		}
		Logger.getRootLogger().debug(sb);
		Logger.getRootLogger().debug("Equation dump ended!");*/
	}
	
	/**
	 * Generate a constraint for this theory. This function should be
	 * overwritten by subclasses to provide theory specific bound 
	 * implementations. 
	 * @param var      Variable to set bound on.
	 * @param bound    Bound to set on <code>var</code>.
	 * @param fac      Factor originally in front of var.
	 *                 This is used to restore the SMT formula and to 
	 *                 determine if <= or >= should be generated.
	 * @param strict   Is the bound strict?
	 * @return Constraint representing this bound.
	 */
	protected Literal generateConstraint(LinVar var, Rational bound, boolean isLowerBound, boolean strict) {
		InfinitNumber rbound = new InfinitNumber(bound, (strict ^ isLowerBound) ? Rational.MONE : Rational.ZERO);
		BoundConstraint bc = var.mconstraints.get(rbound);
		if (bc != null)
			return isLowerBound ? bc.negate() : bc;
		bc = new BoundConstraint(rbound, var);
		assert(checkCoeffChain(bc.mvar));
		mengine.addAtom(bc);
		return isLowerBound ? bc.negate() : bc;
	}
	
	/**
	 * Remove a basic variable from the tableau. Note that <code>v</code> has
	 * to be a basic variable. So you might need to call pivot before removing
	 * a variable.
	 * @param v Basic variable to remove from the tableau.
	 */
	protected void removeVar(LinVar v) {
		assert(v.mbasic);
		mcurbasics.remove(v);
		if( v.isInitiallyBasic() )
			mbasics.remove(v);
		else
			mnonbasics.remove(v);
		for (MatrixEntry entry = v.headEntry.nextInRow;
			entry != v.headEntry; entry = entry.nextInRow) {
			assert(!entry.column.mbasic);
			entry.removeFromMatrix();
		}
	}
	
	/**
	 * This function simplifies the tableau by removing all trivially 
	 * satisfiable equations. In case of rationals, an equation of the
	 * for x_b = sum_i c_i*x_i where there is at least one x_i without
	 * any bound constraint is trivially satisfiable.
	 * 
	 *  In the integer case this is not true anymore since branch and bound
	 *  might introduce constraints on x_i.
	 *  
	 *  This function should be called only once and only 
	 *  <strong>before</strong> first pivoting operation.
	 */
	protected void simplifyTableau() {
		doSimplifyTableau = false;
		assert(checkBRPCounters());
		for( LinVar v : mbasics ) {
			/* Need this if check here since pivoting changes basic and 
			 * nonbasic but we do not reflect this change in mbasics.
			 */
			assert(v.mbasic);
			assert(v.isInitiallyBasic());
			for (MatrixEntry entry = v.headEntry.nextInRow;
				entry != v.headEntry; entry = entry.nextInRow) {
				LinVar nb = entry.column;
				if( nb.mconstraints.isEmpty() ) {
					assert(!nb.mbasic);
					assert(!nb.isInitiallyBasic());
					pivot(entry);
					removeVar(nb);
					assert(checkBRPCounters());
					if( msimps == null )
						msimps = new ArrayList<LinVar>();
					msimps.add(nb);
					break;
				}
			}
//			dumpBasics();
//			Logger.getRootLogger().debug("Simplifications:");
//			dumpSimps();
//			Logger.getRootLogger().debug("Done...");
		}
//		dumpBasics();
		assert(checkPostSimplify());
		assert(checkBRPCounters());
	}
	
	/**
	 * Calculates the values of the simplified variables 
	 */// TODO: Check whether we want a complete model or not???
	private void calculateSimpVals() {
		if( msimps == null )
			return;
		for( int i = msimps.size() - 1; i >= 0; --i ) {
			LinVar v = msimps.get(i);
			assert(v.mbasic);
//			Logger.getRootLogger().debug("Calculating value for " + v);
			MutableInfinitNumber val = new MutableInfinitNumber();
			for (MatrixEntry entry = v.headEntry.nextInRow;
				entry != v.headEntry; entry = entry.nextInRow)
				val.addmul(entry.column.mcurval, entry.coeff);
			v.mcurval = val.toInfinitNumber();
		}
	}
	
	// --- Start of all assertion stuff ---
	private void addIBVar(LinVar var,TreeMap<LinVar,Rational> chain,Rational coeff) {
		assert(var.isInitiallyBasic());
		LinTerm lt = (LinTerm)var.mname;
		for( Map.Entry<LinVar, Rational> me : lt.mcoeffs.entrySet() ) {
			assert (!me.getKey().isInitiallyBasic());
			Rational fac = chain.get(me.getKey());
			if( fac == null ) {
				chain.put(me.getKey(),coeff.mul(me.getValue()));
			} else {
				Rational nfac = fac.add(me.getValue().mul(coeff));
				if( nfac.compareTo(Rational.ZERO) == 0 )
					chain.remove(me.getKey());
				else
					chain.put(me.getKey(),nfac);
			}
		}
	}
	private void flatenhelpersingle(LinVar var,Rational coeff,TreeMap<LinVar,Rational> tm) {
		Rational oldcoeff = tm.get(var);
		if( oldcoeff == null )
			tm.put(var,coeff);
		else {
			Rational newcoeff = oldcoeff.add(coeff);
			if( newcoeff.compareTo(Rational.ZERO) == 0 )
				tm.remove(var);
			else
				tm.put(var,newcoeff);
		}
	}
	private void flatenhelper(LinVar var,Rational coeff,TreeMap<LinVar,Rational> tm) {
		LinTerm lt = (LinTerm)var.mname;
		for( Map.Entry<LinVar,Rational> me : lt.mcoeffs.entrySet() ) {
			if( me.getKey().isInitiallyBasic() )
				flatenhelper(me.getKey(), coeff.mul(me.getValue()), tm);
			else
				flatenhelpersingle(me.getKey(), coeff.mul(me.getValue()), tm);
		}
	}
	private TreeMap<LinVar,Rational> flaten(LinTerm lt) {
		TreeMap<LinVar,Rational> res = new TreeMap<LinVar, Rational>();
		for( Map.Entry<LinVar,Rational> me : lt.mcoeffs.entrySet() ) {
			if( me.getKey().isInitiallyBasic() )
				flatenhelper(me.getKey(),me.getValue(),res);
			else
				flatenhelpersingle(me.getKey(),me.getValue(),res);
				
		}
		return res;
	}
	protected boolean checkCoeffChain(LinVar var) {
		if( !var.isInitiallyBasic() || !var.mbasic )
			return true;
		TreeMap<LinVar,Rational> chain = new TreeMap<LinVar, Rational>();
		for (MatrixEntry entry = var.headEntry.nextInRow;
			entry != var.headEntry; entry = entry.nextInRow) {
			LinVar nb = entry.column;
			if( nb.isInitiallyBasic() )
				addIBVar(nb,chain,entry.coeff);
			else {
				Rational fac = chain.get(nb);
				if( fac == null )
					chain.put(nb,entry.coeff);
				else {
					Rational nfac = fac.add(entry.coeff);
					if( nfac.equals(Rational.ZERO) )
						chain.remove(nb);
					else
						chain.put(nb,nfac);
				}
			}
		}
		LinTerm lt = (LinTerm)var.mname;
		TreeMap<LinVar,Rational> ltm = flaten(lt);
		Iterator<Map.Entry<LinVar,Rational>> it1 = ltm.entrySet().iterator();
		Iterator<Map.Entry<LinVar,Rational>> it2 = chain.entrySet().iterator();
		while( it1.hasNext() ) {
			if( !it2.hasNext() ) {
				System.err.println("Original linear term contains more elements than chain!");
				return false;
			}
			Map.Entry<LinVar,Rational> me1 = it1.next();
			Map.Entry<LinVar,Rational> me2 = it2.next();
			if( me1.getKey() != me2.getKey() ) {
				System.err.println("Error on variable " + var + " with coeff map: " + var.headEntry.rowToString());
				System.err.println("Variables differ: " + me1.getKey() + " against " + me2.getKey());
				System.err.println("Maps:");
				System.err.println("Linear Term: " + ltm);
				System.err.println("Chain: " + chain);
				return false;
			}
			if( !me1.getValue().equals(me2.getValue()) ) {
				System.err.println("Coefficients for " + me1.getKey() + " differ: " + me1.getValue() + " against " + me2.getValue());
				return false;
			}
		}
		if( it2.hasNext() ) {
			System.err.println("Chain contains more elements than original linear term!");
			return false;
		}
		return true;
	}
	@SuppressWarnings("unused")
	private boolean checkoob() {
		for( LinVar v : mbasics ) {
			if( v.outOfBounds() )
				return false;
		}
		for( LinVar v : mnonbasics ) {
			if( v.outOfBounds() )
				return false;
		}
		return true;
	}
	private boolean checkoobcontent() {
		for( LinVar v : mbasics ) {
			if( v.outOfBounds() && !moob.contains(v) ) {
				System.err.println("Variable " + v + " is out of bounds: " + v.mlbound + "<=" + v.mcurval + "<=" + v.mubound);
				return false;
			}
		}
		for( LinVar v : mnonbasics ) {
			if( v.outOfBounds() && !moob.contains(v) ) {
				System.err.println("Variable " + v + " is out of bounds: " + v.mlbound + "<=" + v.mcurval + "<=" + v.mubound);
				return false;
			}
		}
		return true;
	}
	protected boolean checkvals() {
		boolean noerror = true;
		/*final MutableInfinitNumber ZERO = new MutableInfinitNumber(Rational.ZERO,Rational.ZERO);
		for( LinVar v : mbasics ) {
			if( v.mbasic && (msimps == null || !msimps.contains(v)) ) {
				TreeSet<LinVar> nonbasics = new TreeSet<LinVar>();
//				Logger.getRootLogger().debug(" Value of " + v + " is " + v.mcurval);
				MutableInfinitNumber res = new MutableInfinitNumber(v.mcurval);
				Coefficient c = v.mcoeffs;
				while( c != Coefficient.dummyendcoeff ) {
//					Logger.getRootLogger().debug("Adding " + c.coeff + " * " + c.nonbasic.mcurval + "[var is " + c.nonbasic + "]");
					res.sub(c.nonbasic.mcurval.mul(c.coeff));
					if( !nonbasics.add(c.nonbasic) )
						Logger.getRootLogger().debug("Duplicated nonbasic variable " + c.nonbasic + " in chain of " + c.basic);
					c = c.nextnonbasic;
				}
				if( res.compareTo(ZERO) != 0 ) {
					Logger.getRootLogger().debug("Error on " + v + "; diff is " + res + "; val is " + v.mcurval);
					StringBuilder sb = new StringBuilder("Chain is: ");
					Coefficient coeff = v.mcoeffs;
					String add = "";
					while( coeff != Coefficient.dummyendcoeff ) {
						sb.append(add).append(coeff).append("[").append(coeff.nonbasic.mcurval).append("]");
						add = " + ";
						coeff = coeff.nextnonbasic;
					}
					Logger.getRootLogger().debug(sb);
					noerror = false;
				} 
//				else
//					Logger.getRootLogger().debug("No error on " + v);
			}
		}
		for( LinVar v : mnonbasics ) {
			if( v.mbasic && (msimps == null || !msimps.contains(v)) ) {
//				Logger.getRootLogger().debug(" Value of " + v + " is " + v.mcurval);
				MutableInfinitNumber res = new MutableInfinitNumber(v.mcurval);
//				Logger.getRootLogger().debug("res = " + res);
				Coefficient c = v.mcoeffs;
				while( c != Coefficient.dummyendcoeff ) {
//					Logger.getRootLogger().debug("Adding " + c.coeff + " * " + c.nonbasic.mcurval + "[var is " + c.nonbasic + "]");
					res.sub(c.nonbasic.mcurval.mul(c.coeff));
//					Logger.getRootLogger().debug("res = " + res);
					c = c.nextnonbasic;
				}
				if( res.compareTo(ZERO) != 0 ) {
					Logger.getRootLogger().debug("Error on " + v + "; diff is " + res + "; val is " + v.mcurval);
					StringBuilder sb = new StringBuilder("Chain is: ");
					Coefficient coeff = v.mcoeffs;
					String add = "";
					while( coeff != null ) {
						sb.append(add).append(coeff).append("[").append(coeff.nonbasic.mcurval).append("]");
						add = " + ";
						coeff = coeff.nextnonbasic;
					}
					Logger.getRootLogger().debug(sb);
					noerror = false;
				} 
//				else
//					Logger.getRootLogger().debug("No error on " + v);
			}
		}
		if( !noerror ) {
//			dumpBasics();
//			dumpModel(Logger.getRootLogger());
		}*/
		return noerror;
	}
	@SuppressWarnings("unused")
	private boolean reachable(Coefficient x,Coefficient chain,boolean basicchain) {
		while( chain != null ) {
			if( chain == x )
				return true;
			chain = basicchain ? chain.nextbasic : chain.nextnonbasic;
		}
		return false;
	}
	protected boolean checkvarbound(LinVar var) {
		if( !var.mlbound.isInfinity() && var.lowerassert == null ) {
			System.err.println("Inconsistent on lower bound of " + var);
			return false;
		}
		if( !var.mubound.isInfinity() && var.upperassert == null ) {
			System.err.println("Inconsistent on upper bound of " + var);
			return false;
		}
		if( !var.mbasic && (var.mcurval.less(var.mlbound) || var.mubound.less(var.mcurval)) ) {
			System.err.println("Nonbasic variable out of bounds: " + var);
			return false;
		}
		return true;
	}
	protected boolean checkVal(LinVar var) {
		/*if( var.mbasic ) {
			MutableInfinitNumber val = new MutableInfinitNumber();
			Coefficient c = var.mcoeffs;
			while( c != Coefficient.dummyendcoeff ) {
				val.add(c.nonbasic.mcurval.mul(c.coeff));
				c = c.nextnonbasic;
			}
			return val.toInfinitNumber().compareTo(var.mcurval) == 0;
		}*/
		return true;
	}
	protected String equation(LinVar basic) {
		assert(basic.mbasic);
		StringBuilder sb = new StringBuilder(basic.toString());
		/*sb.append(" = ");
		Coefficient c = basic.mcoeffs;
		String add = "";
		while( c != Coefficient.dummyendcoeff ) {
			sb.append(add).append(c.toString());
			add = "+";
			c = c.nextnonbasic;
		}*/
		return sb.toString();
	}
	private boolean checkbrpcs(BoundConstraint bc) {
		assert bc.mpropexpl != null;
		for( Literal l : bc.mpropexpl ) {
			assert l.getAtom() == bc 
				|| l.getAtom().getDecideStatus() == l.negate() : 
				"Error on literal " + l + " (Decide Status is " + l.getAtom().getDecideStatus() + ')'
				+ " in "+Arrays.toString(bc.mpropexpl);
//			System.err.println("No error on " + l);
		}
		return true;
	}
	protected boolean checkColumn(MatrixEntry mentry) {
		LinVar c = mentry.column;
		assert !c.mbasic;
		assert c.headEntry.column == c;
		assert c.headEntry.row == LinVar.dummylinvar;
		assert c.headEntry.nextInRow == null && c.headEntry.prevInRow == null;
		boolean seen = false;
		for (MatrixEntry entry = c.headEntry.nextInCol;
			entry != c.headEntry; entry = entry.nextInCol) {
			assert entry.nextInCol.prevInCol == entry; 
			assert entry.prevInCol.nextInCol == entry; 
			assert entry.column == c;
			if (mentry == entry)
				seen = true;
		}
		assert c.headEntry.nextInCol.prevInCol == c.headEntry; 
		assert c.headEntry.prevInCol.nextInCol == c.headEntry; 
		assert(seen);
		return true;
	}
	protected boolean checkMatrixLinks() {
		for (LinVar v : mcurbasics) {
			assert v.mbasic;
			assert v.headEntry.row == v;
			assert v.headEntry.column == LinVar.dummylinvar;
			assert v.headEntry.nextInCol == null && v.headEntry.prevInCol == null;
			for (MatrixEntry entry = v.headEntry.nextInRow;
				entry != v.headEntry; entry = entry.nextInRow) {
				assert !entry.coeff.equals(Rational.ZERO);
				assert entry.nextInRow.prevInRow == entry; 
				assert entry.prevInRow.nextInRow == entry; 
				assert entry.row == v;
				assert !entry.column.mbasic;
				assert checkColumn(entry);
			}
			assert v.headEntry.nextInRow.prevInRow == v.headEntry; 
			assert v.headEntry.prevInRow.nextInRow == v.headEntry; 
		}
		return true;
	}
	protected boolean checkConsistency() {
		for( LinVar v : mcurbasics ) {
			if( !checkVarConsistency(v) ) {
				checkCoeffChain(v);
				if( v.isInitiallyBasic() ) {
					LinTerm lt = (LinTerm)v.mname;
					for( LinVar cv : lt.mcoeffs.keySet() ) {
						if( !mnonbasics.contains(cv) && (msimps == null || !msimps.contains(cv)) ) {
							System.err.println("Variable " + cv + " not known!");
						}
					}
				}
				return false;
			}
		}
		for( LinVar v : mbasics ) {
			if( !checkCoeffChain(v) )
				return false;
		}
		for( LinVar v : mnonbasics ) {
			if( !checkCoeffChain(v) )
				return false;
		}
		return true;
	}
	protected boolean checkVarConsistency(LinVar v) {
		if( !v.isInitiallyBasic() )
			return true;
		calculateSimpVals();
		if( v.mbasic ) {
			MutableInfinitNumber val = new MutableInfinitNumber();
			for (MatrixEntry entry = v.headEntry.nextInRow;
				entry != v.headEntry; entry = entry.nextInRow) {
				val.addmul(entry.column.mcurval, entry.coeff);
			}
			if( !v.mcurval.equals(val.toInfinitNumber()) ) {
				System.err.println("Variable " + v + " has wrong value: is " + v.mcurval + " chain says " + val);
			}
		}
		LinTerm lt = (LinTerm)v.mname;
		MutableInfinitNumber val = new MutableInfinitNumber();
		for( Map.Entry<LinVar,Rational> me : lt.mcoeffs.entrySet() ) {
			val.addmul(me.getKey().mcurval,me.getValue());
		}
		if( v.mcurval.compareTo(val.toInfinitNumber()) != 0 ) {
			System.err.println("Var: " + v + (v.mbasic ? " [basic]" : " [nonbasic]"));
			System.err.println("Values differ: Is " + v.mcurval + " but should be " + val);
			System.err.println("Coeff map: " + (v.mbasic ? v.headEntry.rowToString() : v.headEntry.colToString()));
//			dumpModel(Logger.getRootLogger());
			for( Map.Entry<LinVar,Rational> me : lt.mcoeffs.entrySet() ) {
				if( msimps != null && msimps.contains(me.getKey()) ) {
					System.err.println(v + " contains simplified variable " + me.getKey());
				}
			}
			return false;
		}
		return true;
	}
	private boolean checkPostSimplify() {
		if( msimps == null )
			return true;
		for( LinVar b : mbasics ) {
			if (b.mbasic) {
				for (MatrixEntry entry = b.headEntry.nextInRow;
					entry != b.headEntry; entry = entry.nextInRow) {
					LinVar nb = entry.column;
					assert !msimps.contains(nb) :
						("Variable " + b + (b.mbasic ? " [basic]" : " [nonbasic]") + " contains simplified variable!");
				}
			} else {
				for (MatrixEntry entry = b.headEntry.nextInCol;
					entry != b.headEntry; entry = entry.nextInCol) {
					LinVar nb = entry.row;
					assert !msimps.contains(nb) :
						("Variable " + b + (b.mbasic ? " [basic]" : " [nonbasic]") + " contains simplified variable!");
				}
			}
		}
		for( LinVar b : mnonbasics ) {
			if (b.mbasic) {
				for (MatrixEntry entry = b.headEntry.nextInRow;
					entry != b.headEntry; entry = entry.nextInRow) {
					LinVar nb = entry.column;
					assert !msimps.contains(nb) :
						("Variable " + b + (b.mbasic ? " [basic]" : " [nonbasic]") + " contains simplified variable!");
				}
			} else {
				for (MatrixEntry entry = b.headEntry.nextInCol;
					entry != b.headEntry; entry = entry.nextInCol) {
					LinVar nb = entry.row;
					assert !msimps.contains(nb) :
						("Variable " + b + (b.mbasic ? " [basic]" : " [nonbasic]") + " contains simplified variable!");
				}
			}
		}
		return true;
	}

	private InterpolationInfo createNelsonOppenInterpolant(EqualityAtom eq,
			Literal leq, Literal geq, MutableAffinTerm mixedTerm) {
		local.stalin.logic.Theory theory = mengine.getSMTTheory();
		FormulaVariable fvar1 = theory.createFreshFormulaVariable("NO");
		FormulaVariable fvar2 = theory.createFreshFormulaVariable("NO");
		HashSet<BoundConstraint> linlits = new HashSet<BoundConstraint>(2);
		linlits.add((BoundConstraint) leq.getAtom());
		linlits.add((BoundConstraint) geq.getAtom());
		LinInterpolant interpolant = 
			new LinInterpolant(new AffinTerm(Rational.ZERO, mixedTerm.isIntegral()), theory.atom(fvar2), linlits);
		Interpolator lininterpolator = new LinArInterpolator(theory, fvar1,
				interpolant);
		Interpolator eqinterpolator = new CCMixedLiteralInterpolator(theory,
				eq.getMixedInterpolationTermVar(), fvar2, mixedTerm.toSMTLib(theory));
		HashMap<DPLLAtom, Interpolator> mixedLitInterpolators = new HashMap<DPLLAtom, Interpolator>();
		mixedLitInterpolators.put(leq.getAtom(), lininterpolator);
		mixedLitInterpolators.put(geq.getAtom(), lininterpolator);
		mixedLitInterpolators.put(eq, eqinterpolator);
		return new InterpolationInfo(theory.atom(fvar1), mixedLitInterpolators);
	}

	private InterpolationInfo createNelsonOppenInterpolant(Literal leq, MutableAffinTerm mixed) {
		local.stalin.logic.Theory theory = mengine.getSMTTheory();
		FormulaVariable fvar = theory.createFreshFormulaVariable("NO");
		LinInterpolant interpolant =
			new LinInterpolant(mixed, Collections.singleton((BoundConstraint) leq.getAtom()));
		Interpolator interpolator = new LinArInterpolator(theory, fvar,
				interpolant);
		return new InterpolationInfo(theory.atom(fvar), 
				Collections.singletonMap(leq.getAtom(), interpolator));
	}

	/**
	 * Generate the Nelson-Oppen clauses for the equality aterm = bterm.
	 * This creates three clauses:
	 * <pre>
	 * aterm = bterm || aterm &lt; bterm || aterm &gt; bterm
	 * aterm != bterm || aterm &gt;= bterm
	 * aterm != bterm || aterm &lt;= bterm
	 * </pre>
	 * It also generates the correct interpolants and handles the
	 * case where the term is mixed.  The terms must be ordered by
	 * formula number such that 
	 * <pre>aterm.getFirstFormula() &lt;= bterm.getFirstFormula().</pre>
	 * @param aterm  The first term.
	 * @param bterm  The second term.
	 * @param eq     the equality atom for aterm = bterm.
	 * @param numipls the number of interpolants to create.  This
	 * is the number of formulas minus one.
	 * @return an array containing the three Nelson-Oppen clauses.
	 */
	public Clause[] generateNelsonOppenClauses(AffinTerm aterm, AffinTerm bterm,
			EqualityAtom eq, int numipls) {
		assert (aterm.getFirstFormulaNr() <= bterm.getLastFormulaNr());
		boolean isInt = this instanceof IntLinArSolve;
		local.stalin.logic.Theory theory = mengine.getSMTTheory();
		Clause[] clauses = new Clause[3];
		MutableAffinTerm at = new MutableAffinTerm(aterm.isIntegral());
		at.add(Rational.ONE, aterm).add(Rational.MONE, bterm);
		Rational gcd = at.getGCD();
		at.mul(gcd.inverse());
		LinVar var = generateLinVar(at.summands);

		int ffnr = var.getFirstFormulaNr();
		int lfnr = var.getLastFormulaNr();
		if (lfnr < ffnr && var.mixedVar == null) {
			Sort sort = isInt ? theory.getSort("Int") : theory.getSort("Real");
			TermVariable mixedVar = theory.createFreshTermVariable("la", sort);
			LinVar mixedLinVar = new LinVar(theory.term(mixedVar), true);
			var.mixedVar = mixedLinVar;
		}
		
		
		Literal leq = generateConstraint(var, at.constant.ma.negate(), gcd.isNegative(), false);
		Literal geq = generateConstraint(var, at.constant.ma.negate(), !gcd.isNegative(), false);
		InterpolationInfo[] ipl = new InterpolationInfo[numipls];
		for (int i = 0; i < numipls; i++) {
			if (i < lfnr) {
				/* Nelson oppen clause is in B. Interpolants is TRUE */
				ipl[i] = InterpolationInfo.TRUE;
			} else if (i < ffnr) {
				/* Mixed case */
				MutableAffinTerm mixedT = new MutableAffinTerm(isInt);
				mixedT.add(Rational.ONE, aterm);
				mixedT.add(gcd, var.mixedVar);
				mixedT.addALocal(gcd.negate(), var, i);
				ipl[i] = createNelsonOppenInterpolant(eq, leq, geq,	mixedT);
			} else {
				/* Nelson oppen clause is in A; no literal in B. */
				ipl[i] = InterpolationInfo.FALSE;
			}
		}
		clauses[0] = new Clause(new Literal[] { eq, geq.negate(), leq.negate() }, ipl);
		LinVar eqMixedVar = null;
		if (lfnr < ffnr) {
			eqMixedVar = 
				new LinVar(theory.term(eq.getMixedInterpolationTermVar()), aterm.isIntegral());
			ipl = ipl.clone();
			for (int i = lfnr; i < ffnr; i++) {
				MutableAffinTerm mixedT = new MutableAffinTerm(isInt);
				mixedT.add(Rational.ONE, aterm);
				mixedT.add(gcd, var.mixedVar);
				mixedT.addALocal(gcd.negate(), var, i);
				mixedT.add(Rational.MONE, eqMixedVar);
				
				InterpolationInfo info = createNelsonOppenInterpolant(leq, mixedT); 
				ipl[i] = info;
			}
		}
		clauses[1] = new Clause(new Literal[] { eq.negate(), leq }, ipl);
		if (lfnr < ffnr) {
			ipl = ipl.clone();
			for (int i = lfnr; i < ffnr; i++) {
				/* The other clauses have different interpolators */
				MutableAffinTerm mixedT = new MutableAffinTerm(isInt);
				mixedT.add(Rational.ONE, eqMixedVar);
				mixedT.add(Rational.MONE, aterm);
				mixedT.addALocal(gcd, var, i);
				mixedT.add(gcd.negate(), var.mixedVar);

				InterpolationInfo info = createNelsonOppenInterpolant(geq, mixedT); 
				ipl[i] = info;
			}
		}
		clauses[2] = new Clause(new Literal[] { eq.negate(), geq }, ipl);
		return clauses;
	}

	private boolean checkBRPCounters() {
		for( LinVar v : mcurbasics ) {
			assert v.numlower >= 0 :
				("Negative lower count on " + v);
			assert v.numupper >= 0 :
				("Negative upper count on " + v);
			int upper,lower;
			upper = lower = 0;
			for (MatrixEntry entry = v.headEntry.nextInRow;
				entry != v.headEntry; entry = entry.nextInRow) {
				LinVar nb = entry.column;
				if( entry.coeff.isNegative() ) {
					if( nb.upperassert == null )
						++lower;
					if( nb.lowerassert == null )
						++upper;
				} else {
					if( nb.upperassert == null )
						++upper;
					if( nb.lowerassert == null )
						++lower;
				}
			}
			assert upper == v.numupper :
				("Wrong upper count on " + v + " Is " + v.numupper + " but should be " + upper);
			assert lower == v.numlower :
				("Wrong lower count on " + v + " Is " + v.numlower + " but should be " + lower);
		}
		return true;
	}
}
