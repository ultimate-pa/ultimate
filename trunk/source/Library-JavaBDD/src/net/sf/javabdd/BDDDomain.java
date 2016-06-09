// BDDDomain.java, created Jan 29, 2003 9:50:57 PM by jwhaley
// Copyright (C) 2003 John Whaley
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.javabdd;

import java.math.BigInteger;
import java.util.Iterator;

/**
 * Represents a domain of BDD variables.  This is useful for finite state
 * machines, among other things.
 *
 * <p>BDDDomains are called "finite domain blocks" in Section 2.9
 * of the buddy documentation.   A BDDDomain is a block of BDD variables 
 * that can represent integer values as opposed to only true and false.</p>
 * 
 * <p>Use <tt>BDDFactory.extDomain()</tt> to create one or more domains with 
 * a specified list of sizes.</p>
 * 
 * @author John Whaley
 * @version $Id: BDDDomain.java,v 1.7 2005/04/17 10:21:46 joewhaley Exp $
 * @see net.sf.javabdd.BDDFactory#extDomain(int[])
 */
public abstract class BDDDomain {

    /* The name of this domain. */
    protected String name;
    /* The index of this domain. */
    protected int index;

    /* The specified domain (0...N-1) */
    protected BigInteger realsize;
    /* Variable indices for the variable set */
    protected int[] ivar;
    /* The BDD variable set.  Actually constructed in extDomain(), etc. */
    protected BDD var;

    /**
     * Default constructor.
     * 
     * @param index  index of this domain
     * @param range  size of this domain
     */
    protected BDDDomain(int index, BigInteger range) {
        BigInteger calcsize = BigInteger.valueOf(2L);
        if (range.signum() <= 0) {
			throw new BDDException();
		}
        name = Integer.toString(index);
        this.index = index;
        realsize = range;
        int binsize = 1;
        while (calcsize.compareTo(range) < 0) {
           binsize++;
           calcsize = calcsize.shiftLeft(1);
        }
        ivar = new int[binsize];
    }

    /**
     * Returns the factory that created this domain.
     */
    public abstract BDDFactory getFactory();

    /**
     * Sets the name of this domain.
     */
    public void setName(String name) {
        this.name = name;
    }
    
    /**
     * Gets the name of this domain.
     */
    public String getName() {
        return name;
    }
    
    /**
     * Returns the index of this domain.
     */ 
    public int getIndex() {
        return index;
    }

    /**
     * <p>Returns what corresponds to a disjunction of all possible values of this
     * domain. This is more efficient than doing ithVar(0) OR ithVar(1) ...
     * explicitly for all values in the domain.</p>
     * 
     * <p>Compare to fdd_domain.</p>
     */ 
    public BDD domain() {
        final BDDFactory factory = getFactory();
        
        /* Encode V<=X-1. V is the variables in 'var' and X is the domain size */
        BigInteger val = size().subtract(BigInteger.ONE);
        final BDD d = factory.one();
        final int[] ivar = vars();
        for (int n = 0; n < varNum(); n++) {
            if (val.testBit(0)) {
				d.orWith(factory.nithVar(ivar[n]));
			} else {
				d.andWith(factory.nithVar(ivar[n]));
			}
            val = val.shiftRight(1);
        }
        return d;
    }

    /**
     * Returns the size of the domain for this finite domain block.
     * 
     * Compare to fdd_domainsize.
     */
    public BigInteger size() {
        return realsize;
    }
    
    public BDD buildAdd(BDDDomain that, long value) {
        if (varNum() != that.varNum()) {
			throw new BDDException();
		}
        return buildAdd(that, varNum(), value);
    }
    public BDD buildAdd(BDDDomain that, int bits, long value) {
        if (bits > varNum() ||
            bits > that.varNum()) {
			throw new BDDException("Number of bits requested ("+bits+") is larger than domain sizes "+varNum()+","+that.varNum());
		}
        
        final BDDFactory bdd = getFactory();
        
        if (value == 0L) {
            final BDD result = bdd.one();
            int n;
            for (n = 0; n < bits; n++) {
                final BDD b = bdd.ithVar(ivar[n]);
                b.biimpWith(bdd.ithVar(that.ivar[n]));
                result.andWith(b);
            }
            for ( ; n < Math.max(varNum(), that.varNum()); n++) {
                final BDD b = (n < varNum()) ? bdd.nithVar(ivar[n]) : bdd.one();
                b.andWith((n < that.varNum()) ? bdd.nithVar(that.ivar[n]) : bdd.one());
                result.andWith(b);
            }
            return result;
        }

        final int[] vars = new int[bits];
        System.arraycopy(ivar, 0, vars, 0, vars.length);
        final BDDBitVector y = bdd.buildVector(vars);
        final BDDBitVector v = bdd.constantVector(bits, value);
        final BDDBitVector z = y.add(v);
        
        final int[] thatvars = new int[bits];
        System.arraycopy(that.ivar, 0, thatvars, 0, thatvars.length);
        final BDDBitVector x = bdd.buildVector(thatvars);
        final BDD result = bdd.one();
        int n;
        for (n = 0; n < x.size(); n++) {
            final BDD b = x.bitvec[n].biimp(z.bitvec[n]);
            result.andWith(b);
        }
        for ( ; n < Math.max(varNum(), that.varNum()); n++) {
            final BDD b = (n < varNum()) ? bdd.nithVar(ivar[n]) : bdd.one();
            b.andWith((n < that.varNum()) ? bdd.nithVar(that.ivar[n]) : bdd.one());
            result.andWith(b);
        }
        x.free(); y.free(); z.free(); v.free();
        return result;
    }
    
    /**
     * Builds a BDD which is true for all the possible assignments to the
     * variable blocks that makes the blocks equal.
     * 
     * Compare to fdd_equals/fdd_equ.
     * 
     * @param that
     * @return BDD
     */
    public BDD buildEquals(BDDDomain that) {
        if (!size().equals(that.size())) {
            throw new BDDException("Size of "+this+" != size of that "+that+"( "+size()+" vs "+that.size()+")");
        }

        final BDDFactory factory = getFactory();
        final BDD e = factory.one();

        final int[] this_ivar = vars();
        final int[] that_ivar = that.vars();

        for (int n = 0; n < varNum(); n++) {
            final BDD a = factory.ithVar(this_ivar[n]);
            final BDD b = factory.ithVar(that_ivar[n]);
            a.biimpWith(b);
            e.andWith(a);
        }

        return e;
    }
    
    /**
     * Returns the variable set that contains the variables used to define this
     * finite domain block.
     * 
     * Compare to fdd_ithset.
     * 
     * @return BDD
     */
    public BDD set() {
        return var.id();
    }
    
    /**
     * Returns the BDD that defines the given value for this finite domain
     * block.
     * 
     * Compare to fdd_ithvar.
     * 
     * @return BDD
     */
    public BDD ithVar(long val) {
        return ithVar(BigInteger.valueOf(val));
    }
    public BDD ithVar(BigInteger val) {
        if (val.signum() < 0 || val.compareTo(size()) >= 0) {
            throw new BDDException(val+" is out of range");
        }

        final BDDFactory factory = getFactory();
        final BDD v = factory.one();
        final int[] ivar = vars();
        for (int n = 0; n < ivar.length; n++) {
            if (val.testBit(0)) {
				v.andWith(factory.ithVar(ivar[n]));
			} else {
				v.andWith(factory.nithVar(ivar[n]));
			}
            val = val.shiftRight(1);
        }

        return v;
    }
    
    /**
     * Returns the BDD that defines the given range of values, inclusive,
     * for this finite domain block.
     * 
     * @return BDD
     */
    public BDD varRange(long lo, long hi) {
        return varRange(BigInteger.valueOf(lo), BigInteger.valueOf(hi));
    }
    public BDD varRange(BigInteger lo, BigInteger hi) {
        if (lo.signum() < 0 || hi.compareTo(size()) >= 0 || lo.compareTo(hi) > 0) {
            throw new BDDException("range <"+lo+", "+hi+"> is invalid");
        }

        final BDDFactory factory = getFactory();
        final BDD result = factory.zero();
        final int[] ivar = vars();
        while (lo.compareTo(hi) <= 0) {
            final BDD v = factory.one();
            for (int n = ivar.length - 1; ; n--) {
                if (lo.testBit(n)) {
                    v.andWith(factory.ithVar(ivar[n]));
                } else {
                    v.andWith(factory.nithVar(ivar[n]));
                }
                final BigInteger mask = BigInteger.ONE.shiftLeft(n).subtract(BigInteger.ONE);
                if (!lo.testBit(n) && lo.or(mask).compareTo(hi) <= 0) {
                    lo = lo.or(mask).add(BigInteger.ONE);
                    break;
                }
            }
            result.orWith(v);
        }
        return result;
    }
    
    /**
     * Returns the number of BDD variables used for this finite domain block.
     * 
     * Compare to fdd_varnum.
     * 
     * @return int
     */
    public int varNum() {
        return ivar.length;
    }
    
    /**
     * Returns an integer array containing the indices of the BDD variables used
     * to define this finite domain.
     * 
     * Compare to fdd_vars.
     * 
     * @return int[]
     */
    public int[] vars() {
        return ivar;
    }
    
    public int ensureCapacity(long range) {
        return ensureCapacity(BigInteger.valueOf(range));
    }
    public int ensureCapacity(BigInteger range) {
        BigInteger calcsize = BigInteger.valueOf(2L);
        if (range.signum() < 0) {
			throw new BDDException();
		}
        if (range.compareTo(realsize) < 0) {
			return ivar.length;
		}
        realsize = range.add(BigInteger.ONE);
        int binsize = 1;
        while (calcsize.compareTo(range) <= 0) {
           binsize++;
           calcsize = calcsize.shiftLeft(1);
        }
        if (ivar.length == binsize) {
			return binsize;
		}
        
        final int[] new_ivar = new int[binsize];
        System.arraycopy(ivar, 0, new_ivar, 0, ivar.length);
        final BDDFactory factory = getFactory();
        for (int i = ivar.length; i < new_ivar.length; ++i) {
            //System.out.println("Domain "+this+" Duplicating var#"+new_ivar[i-1]);
            final int newVar = factory.duplicateVar(new_ivar[i-1]);
            factory.firstbddvar++;
            new_ivar[i] = newVar;
            //System.out.println("Domain "+this+" var#"+i+" = "+newVar);
        }
        ivar = new_ivar;
        //System.out.println("Domain "+this+" old var = "+var);
        var.free();
        final BDD nvar = factory.one();
        for (int i = 0; i < ivar.length; ++i) {
            nvar.andWith(factory.ithVar(ivar[i]));
        }
        var = nvar;
        //System.out.println("Domain "+this+" new var = "+var);
        return binsize;
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
	public String toString() {
        return getName();
    }

    /**
     * Convert a BDD that to a list of indices of this domain.
     * This method assumes that the BDD passed is a disjunction
     * of ithVar(i_1) to ithVar(i_k).  It returns an array
     * of length 'k' with elements [i_1,...,i_k].
     * <p>
     * Be careful when using this method for BDDs with a large number
     * of entries, as it allocates a BigInteger[] array of dimension k.
     *
     * @param bdd bdd that is the disjunction of domain indices
     * @see #getVarIndices(BDD,int)
     * @see #ithVar(BigInteger)
     */
    public BigInteger[] getVarIndices(BDD bdd) {
        return getVarIndices(bdd, -1);
    }

    /**
     * Convert a BDD that to a list of indices of this domain.
     * Same as getVarIndices(BDD), except only 'max' indices
     * are extracted.  
     *
     * @param bdd bdd that is the disjunction of domain indices
     * @param max maximum number of entries to be returned
     *
     * @see #ithVar(long)
     */
    public BigInteger[] getVarIndices(BDD bdd, int max) {
        final BDD myvarset = set(); // can't use var here, must respect subclass a factory may provide
        int n = (int)bdd.satCount(myvarset);
        if (max != -1 && n > max) {
			n = max;
		}
        final BigInteger[] res = new BigInteger[n];
        final Iterator it = bdd.iterator(myvarset);
        for (int i = 0; i < n; i++) {
            final BDD bi = (BDD) it.next();
            res[i] = bi.scanVar(this);
        }
        myvarset.free();
        return res;
    }
}
