package local.stalin.smt.theory.linar;

import java.util.Map;
import java.util.NavigableMap;
import java.util.TreeMap;
import java.util.TreeSet;

import local.stalin.smt.dpll.Literal;

/**
 * Class representing a variable in a linear combination. This might either be
 * a slack variable or a real variable as introduced by the problem. For slack
 * variables we use the object name to refer to the corresponding linear term.
 * 
 * Natural order depends on the order of creation of variables. That is every
 * variable is ordered according to their creation time. Ordering on the
 * variables is one requirement to be able to prove termination of the
 * algorithm.
 * 
 * Every variable knows all possible bound constraints referring to it. This
 * way, bound propagations can easily be implemented.
 * 
 * @author Juergen Christ
 */
public class LinVar implements Comparable<LinVar> {
	// Number used for ordering
	private static int varnum = 0;
	// Name of the variable
	Object mname;
	// Known upper bound
	InfinitNumber mubound;
	// Known lower bound
	InfinitNumber mlbound;
	// Current value
	InfinitNumber mcurval;
	// Is value required to be integer?
	boolean misint;
	// List of all bounds on this variable
	NavigableMap<InfinitNumber,BoundConstraint> mconstraints = 
		new TreeMap<InfinitNumber,BoundConstraint>();
	// Is this variable currently basic? NOTE: THIS IS THE CURRENT STATUS
	boolean mbasic;
	// Save the literals asserted so far...
	Literal upperassert;
	Literal lowerassert;
	// Number to sort this variable in the sparse matrix
	int matrixpos;
	private int firstFormula,lastFormula;
	int numcuts = 0;
	int numlower,numupper;
	/**
	 * The dummy entry that starts the list for this linvar. 
	 * The list follows nextInRow if this is a basic variable,
	 * nextInCol if this is a non-basic variable.
	 */
	MatrixEntry headEntry;
	
	/**
	 * The fresh shared variable used in mixedSum. 
	 */
	LinVar mixedVar;

	/// --- Construction ---
	/**
	 * Constructs a dummy linear variable.
	 */
	private LinVar() {
		mname = "Dummy";
		matrixpos = Integer.MAX_VALUE;
	}
	/**
	 * Constructor for a non-basic variable. <code>name</code> is assumed not
	 * to be an instance of <code>LinTerm</code>.
	 * @param name  Name of the variable (Needed for printout).
	 * @param isint Is the variable required to be integral valued?
	 */
	public LinVar(Object name,boolean isint) {
		mname = name;
		mubound = InfinitNumber.POSITIVE_INFINITY;
		mlbound = InfinitNumber.NEGATIVE_INFINITY;
		mcurval = new InfinitNumber();
		misint = isint;
		mbasic = false;
		matrixpos = ++varnum;
		firstFormula = Integer.MAX_VALUE; lastFormula = -1;

		headEntry = new MatrixEntry();
		headEntry.column = this;
		headEntry.row = dummylinvar;
		headEntry.prevInCol = headEntry;
		headEntry.nextInCol = headEntry;
	}
	/**
	 * Constructor for an initially basic variable. If <code>online</code> is
	 * <code>false</code>, I assume no bound is set on the lin term.
	 * @param lt     Linear term this variable should be equal to.
	 */
	public LinVar(LinTerm lt) {
		this(lt,false);
		mbasic = true;
		numlower = numupper = lt.mcoeffs.size();
		headEntry = new MatrixEntry();
		headEntry.column = dummylinvar;
		headEntry.row = this;
		headEntry.nextInRow = headEntry.prevInRow = headEntry;
		
		MutableInfinitNumber val = new MutableInfinitNumber();
		for( Map.Entry<LinVar,Rational> me : lt.mcoeffs.entrySet() ) {
			LinVar nb = me.getKey();
			assert(!nb.mbasic);
			Rational value = me.getValue();
			headEntry.insertRow(nb, value);
			val.addmul(nb.mcurval, value);
			if( nb.upperassert != null ) {
				if( value.isNegative() )
					--numlower;
				else
					--numupper;
			}
			if( nb.lowerassert != null ) {
				if( value.isNegative() )
					--numupper;
				else
					--numlower;
			}
		}
		mcurval = val.toInfinitNumber();
		assert(chainEqLt(lt));
		firstFormula = Integer.MAX_VALUE; lastFormula = -1;
	}
	/**
	 * Get the upper bound.
	 * @return Upper bound.
	 */
	public InfinitNumber getUBound() {
		return mubound;
	}
	/**
	 * Get the lower bound.
	 * @return Lower bound.
	 */
	public InfinitNumber getLBound() {
		return mlbound;
	}
	/**
	 * Check whether the upper bound is set.
	 * @return <code>true</code> iff upper bound is finite.
	 */
	public boolean isUBoundSet() {
		return upperassert != null;
	}
	/**
	 * Check whether the lower bound is set.
	 * @return <code>true</code> iff lower bound is finite.
	 */
	public boolean isLBoundSet() {
		return lowerassert != null;
	}
	/// --- Bound testing ---
	/**
	 * Check whether we can increment the value of this variable
	 * @return <code>true</code> iff value of this variable is below its upper
	 * 		   bound
	 */
	public boolean isIncrementPossible() {
		return mcurval.less(mubound);
	}
	/**
	 * Check whether we can decrement the value of this variable.
	 * @return <code>true</code> iff value of this variable is above its lower
	 * 		   bound.
	 */
	public boolean isDecrementPossible() {
		return mlbound.less(mcurval);
	}
	/**
	 * Check whether we are at the lower bound.
	 * @return <code>true</code> iff value equals lower bound.
	 */
	public boolean isAtLowerBound() {
		return mlbound.equals(mcurval);
	}
	/**
	 * Check whether we are at the upper bound.
	 * @return <code>true</code> iff value equals upper bound.
	 */
	public boolean isAtUpperBound() {
		return mubound.equals(mcurval);
	}
	/// --- Name stuff ---
	public String toString() {
		return mname.toString();
	}
	/// --- Initially basic testing ---
	/**
	 * Check whether this variable is initially basic.
	 * @return <code>true</code> iff this variable corresponds to a linear term
	 */
	public boolean isInitiallyBasic() {
		// TODO: This is a little bit dirty...
		return mname instanceof LinTerm;
	}
	/// --- Updating values ---
	/**
	 * Update values of all basic variables depending on this non-basic variable.
	 * @param num  Value to set for this variable.
	 * @param oobq Set of all (basic) variables outside their bounds.
	 * @param newubound <code>true</code> iff the first upper bound is assigned
	 * @param newlbound <code>true</code> iff the first upper bound is assigned
	 */
	void update(LinArSolve solver, InfinitNumber num, TreeSet<LinVar> oobq,boolean newubound,boolean newlbound) {
		assert(!mbasic);
		InfinitNumber diff = num.sub(mcurval);
		for (MatrixEntry entry = headEntry.nextInCol;
			entry != headEntry; entry = entry.nextInCol) {
			LinVar var = entry.row;
			assert(var.mbasic);
			var.mcurval = var.mcurval.addmul(diff,entry.coeff);
			if( newubound ) {
				if( entry.coeff.isNegative() )
					--var.numlower;
				else
					--var.numupper;
			} else if( newlbound ) {
				if( entry.coeff.isNegative() )
					--var.numupper;
				else
					--var.numlower;
			}
			if (var.outOfBounds())
				oobq.add(var);
			if (var.numupper == 0 || var.numlower == 0)
				solver.propagate(var);
		}
		mcurval = num;
	}
	
	@Override
	public int hashCode() {
		return matrixpos;
	}
	
	@Override
	public final int compareTo(LinVar o) {
		return matrixpos - o.matrixpos;
	}
	/**
	 * Check whether this variable has a value outside its bounds.
	 * @return <code>false</code> iff <code>mlbound<=mcurval<=mubound</code>. 
	 */
	public boolean outOfBounds() {
		return (mcurval.compareTo(mubound) > 0) || (mcurval.compareTo(mlbound) < 0);
	}
	/**
	 * Remember formula counters. For generated slack variables, we set the
	 * number on all variables contained in the corresponding linear term.
	 * @param formulaNr Number of formula this variable occurs in.
	 */
	public void occursIn(int formulaNr) {
		if (formulaNr < firstFormula)
			firstFormula = formulaNr;
		if (formulaNr > lastFormula)
			lastFormula = formulaNr;
		if( mname instanceof LinTerm ) {
			LinTerm lt = (LinTerm)mname;
			for( LinVar v : lt.mcoeffs.keySet() )
				v.occursIn(formulaNr);
		}
	}
	private boolean chainEqLt(LinTerm lt) {
		/*Coefficient coeff = mcoeffs;
		for( Map.Entry<LinVar,Rational> me : lt.mcoeffs.entrySet() ) {
			if( coeff.nonbasic != me.getKey() ) {
				System.err.println("Nonbasic variable not present");
				return false;
			}
			if( coeff.coeff.compareTo(me.getValue()) != 0 ) {
				System.err.println("Wrong coefficient for variable");
				return false;
			}
			coeff = coeff.nextnonbasic;
		}*/
		return true;
	}
	public int getFirstFormulaNr() {
		if( firstFormula == Integer.MAX_VALUE )
			calculateFormulaNrs();
		return firstFormula;
	}
	public int getLastFormulaNr() {
		if( lastFormula == -1 )
			calculateFormulaNrs();
		return lastFormula;
	}
	private void calculateFormulaNrs() {
		if( isInitiallyBasic() ) {
			LinTerm lt = (LinTerm)mname;
			firstFormula = 0;
			lastFormula = Integer.MAX_VALUE;
			for( LinVar lv : lt.mcoeffs.keySet() ) {
				firstFormula = Math.max(firstFormula,lv.getFirstFormulaNr());
				lastFormula = Math.min(lastFormula,lv.getLastFormulaNr());
			}
		}
	}
	/**
	 * Dummy linear variable marking end of a non-basic chain.
	 */
	final static LinVar dummylinvar = new LinVar();
}
