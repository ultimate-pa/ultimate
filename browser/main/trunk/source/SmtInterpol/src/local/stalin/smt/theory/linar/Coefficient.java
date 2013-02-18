package local.stalin.smt.theory.linar;

/**
 * A coefficient in a sparse coefficient matrix. 
 * 
 * We have a basic chain representing all basic variables where 
 * <code>nonbasic</code> has a non-zero coefficient. This chain is unordered
 * but to be able to remove a basic variable, this chain is doubly linked.
 * 
 * We also have a nonbasic chain representing the linear combination of
 * <code>basic</code>. This chain is ordered to allow faster pivoting.
 * @author Juergen Christ
 */
public class Coefficient {
	Rational coeff;
	LinVar basic;
	LinVar nonbasic;
	// Coefficient of the next basic variable, for which nonbasic has a non-zero coefficient
	Coefficient nextbasic;
	// Coefficient of the previous basic variable, for which nonbasic has a non-zero coefficient
	Coefficient prevbasic;
	// Coefficient of the next nonbasic variable contributing to basic
	Coefficient nextnonbasic;
	
	/**
	 * Create an isolated coefficient. Resulting coefficient has neither a 
	 * basic nor a nonbasic chain. Only the variables and the coefficient are
	 * set.
	 * @param coeff    Coefficient to use
	 * @param basic    Basic variable this coefficient is for
	 * @param nonbasic Non-Basic variable this coefficient is for
	 */
	Coefficient(Rational coeff,LinVar basic,LinVar nonbasic) {
		assert(basic == null || basic.mbasic);
		assert(nonbasic == null || !nonbasic.mbasic);
		this.coeff = coeff;
		this.basic = basic;
		this.nonbasic = nonbasic;
		nextbasic = prevbasic = nextnonbasic = null;
	}
	/**
	 * Dummy end-of-nonbasic-chain coefficient
	 */
	private Coefficient() {
		nonbasic = LinVar.dummylinvar;
		nextbasic = prevbasic = nextnonbasic = this;
	}
	public String toString() {
		return coeff + "*(" + nonbasic + ")";
	}
	final static Coefficient dummyendcoeff = new Coefficient();
}
