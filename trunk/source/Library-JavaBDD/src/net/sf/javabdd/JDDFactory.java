// JDDFactory.java, created Aug 1, 2003 7:06:47 PM by joewhaley
// Copyright (C) 2003 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.javabdd;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

/**
 * JDDFactory
 * 
 * @author John Whaley
 * @version $Id: JDDFactory.java,v 1.5 2005/04/08 05:27:52 joewhaley Exp $
 */
public class JDDFactory extends BDDFactory {

    private final jdd.bdd.BDD bdd;
    private int[] vars; // indexed by EXTERNAL
    private int[] level2var; // internal -> external
    private int[] var2level; // external -> internal
    
    private JDDFactory(int nodenum, int cachesize) {
        bdd = new jdd.bdd.BDD(nodenum, cachesize);
        vars = new int[256];
        jdd.util.Options.verbose = true;
    }
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#init(int, int)
     */
    public static BDDFactory init(int nodenum, int cachesize) {
        final BDDFactory f = new JDDFactory(nodenum, cachesize);
        return f;
    }

    /**
     * Wrapper for the BDD index number used internally in the representation.
     */
    private class bdd extends BDD {
        int _index;

        static final int INVALID_BDD = -1;

        bdd(int index) {
            _index = index;
            bdd.ref(_index);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#getFactory()
         */
        @Override
		public BDDFactory getFactory() {
            return JDDFactory.this;
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#isZero()
         */
        @Override
		public boolean isZero() {
            return _index == bdd.getZero();
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#isOne()
         */
        @Override
		public boolean isOne() {
            return _index == bdd.getOne();
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#var()
         */
        @Override
		public int var() {
            final int v = bdd.getVar(_index);
            return level2var != null ? level2var[v] : v;
        }

        @Override
		public int level() {
            final int v = bdd.getVar(_index);
            return v;
        }
        
        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#high()
         */
        @Override
		public BDD high() {
            return new bdd(bdd.getHigh(_index));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#low()
         */
        @Override
		public BDD low() {
            return new bdd(bdd.getLow(_index));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#id()
         */
        @Override
		public BDD id() {
            return new bdd(_index);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#not()
         */
        @Override
		public BDD not() {
            return new bdd(bdd.not(_index));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#ite(net.sf.javabdd.BDD, net.sf.javabdd.BDD)
         */
        @Override
		public BDD ite(BDD thenBDD, BDD elseBDD) {
            final int x = _index;
            final int y = ((bdd) thenBDD)._index;
            final int z = ((bdd) elseBDD)._index;
            return new bdd(bdd.ite(x, y, z));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#relprod(net.sf.javabdd.BDD, net.sf.javabdd.BDD)
         */
        @Override
		public BDD relprod(BDD that, BDD var) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            final int z = ((bdd) var)._index;
            return new bdd(bdd.relProd(x, y, z));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#compose(net.sf.javabdd.BDD, int)
         */
        @Override
		public BDD compose(BDD g, int var) {
            final int x = _index;
            final int y = ((bdd) g)._index;
            return null; // todo.
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#veccompose(net.sf.javabdd.BDDPairing)
         */
        @Override
		public BDD veccompose(BDDPairing pair) {
            final int x = _index;
            return null; // todo.
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#constrain(net.sf.javabdd.BDD)
         */
        @Override
		public BDD constrain(BDD that) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            return null; // todo.
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#exist(net.sf.javabdd.BDD)
         */
        @Override
		public BDD exist(BDD var) {
            final int x = _index;
            final int y = ((bdd) var)._index;
            return new bdd(bdd.exists(x, y));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#forAll(net.sf.javabdd.BDD)
         */
        @Override
		public BDD forAll(BDD var) {
            final int x = _index;
            final int y = ((bdd) var)._index;
            return new bdd(bdd.forall(x, y));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#unique(net.sf.javabdd.BDD)
         */
        @Override
		public BDD unique(BDD var) {
            final int x = _index;
            final int y = ((bdd) var)._index;
            return null; // todo.
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#restrict(net.sf.javabdd.BDD)
         */
        @Override
		public BDD restrict(BDD var) {
            final int x = _index;
            final int y = ((bdd) var)._index;
            return new bdd(bdd.restrict(x, y));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#restrictWith(net.sf.javabdd.BDD)
         */
        @Override
		public BDD restrictWith(BDD that) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            final int a = bdd.restrict(x, y);
            //System.out.println("restrictWith("+System.identityHashCode(this)+") "+x+" -> "+a);
            bdd.deref(x);
            if (this != that) {
				that.free();
			}
            bdd.deref(a);
            _index = a;
            return this;
        }
        
        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#simplify(net.sf.javabdd.BDD)
         */
        @Override
		public BDD simplify(BDD d) {
            final int x = _index;
            final int y = ((bdd) d)._index;
            return new bdd(bdd.simplify(x, y));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#support()
         */
        @Override
		public BDD support() {
            final int x = _index;
            return new bdd(bdd.support(x));
        }

        private int apply0(int x, int y, int z) {
            int r;
            switch (z) {
                case 0: r = bdd.and(x, y); break;
                case 1: r = bdd.xor(x, y); break;
                case 2: r = bdd.or(x, y); break;
                case 3: r = bdd.nand(x, y); break;
                case 4: r = bdd.nor(x, y); break;
                case 5: r = bdd.imp(x, y); break;
                case 6: r = bdd.biimp(x, y); break;
                case 7: r = bdd.and(x, bdd.not(y)); break; // diff
                default:
                    throw new BDDException(); // TODO.
            }
            return r;
        }
        
        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#apply(net.sf.javabdd.BDD, net.sf.javabdd.BDDFactory.BDDOp)
         */
        @Override
		public BDD apply(BDD that, BDDOp opr) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            final int z = opr.id;
            return new bdd(apply0(x, y, z));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#applyWith(net.sf.javabdd.BDD, net.sf.javabdd.BDDFactory.BDDOp)
         */
        @Override
		public BDD applyWith(BDD that, BDDOp opr) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            final int z = opr.id;
            final int a = apply0(x, y, z);
            bdd.deref(x);
            if (this != that) {
				that.free();
			}
            bdd.ref(a);
            _index = a;
            return this;
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#applyAll(net.sf.javabdd.BDD, net.sf.javabdd.BDDFactory.BDDOp, net.sf.javabdd.BDD)
         */
        @Override
		public BDD applyAll(BDD that, BDDOp opr, BDD var) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            final int z = opr.id;
            final int a = ((bdd) var)._index;
            // todo: combine.
            final int r = apply0(x, y, z);
            bdd.ref(r);
            final int r2 = bdd.forall(r, a);
            bdd.deref(r);
            return new bdd(r2);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#applyEx(net.sf.javabdd.BDD, net.sf.javabdd.BDDFactory.BDDOp, net.sf.javabdd.BDD)
         */
        @Override
		public BDD applyEx(BDD that, BDDOp opr, BDD var) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            final int z = opr.id;
            final int a = ((bdd) var)._index;
            // todo: combine.
            final int r = apply0(x, y, z);
            bdd.ref(r);
            final int r2 = bdd.exists(r, a);
            bdd.deref(r);
            return new bdd(r2);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#applyUni(net.sf.javabdd.BDD, net.sf.javabdd.BDDFactory.BDDOp, net.sf.javabdd.BDD)
         */
        @Override
		public BDD applyUni(BDD that, BDDOp opr, BDD var) {
            final int x = _index;
            final int y = ((bdd) that)._index;
            final int z = opr.id;
            final int a = ((bdd) var)._index;
            throw new BDDException(); // todo.
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#satOne()
         */
        @Override
		public BDD satOne() {
            final int x = _index;
            return new bdd(bdd.oneSat(x));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#replace(net.sf.javabdd.BDDPairing)
         */
        @Override
		public BDD replace(BDDPairing pair) {
            final int x = _index;
            return new bdd(bdd.replace(x, ((bddPairing) pair).pairing));
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#replaceWith(net.sf.javabdd.BDDPairing)
         */
        @Override
		public BDD replaceWith(BDDPairing pair) {
            final int x = _index;
            final int y = bdd.replace(x, ((bddPairing) pair).pairing);
            //System.out.println("replaceWith("+System.identityHashCode(this)+") "+x+" -> "+y);
            bdd.deref(x);
            bdd.ref(y);
            _index = y;
            return this;
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#nodeCount()
         */
        @Override
		public int nodeCount() {
            return bdd.nodeCount(_index);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#satCount()
         */
        @Override
		public double satCount() {
            return bdd.satCount(_index);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#equals(net.sf.javabdd.BDD)
         */
        @Override
		public boolean equals(BDD that) {
            return _index == ((bdd) that)._index;
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#hashCode()
         */
        @Override
		public int hashCode() {
            return _index;
        }

        static final boolean USE_FINALIZER = false;
        
        /**
         * @see java.lang.Object#finalize()
         */
        /*
        protected void finalize() throws Throwable {
            super.finalize();
            if (USE_FINALIZER) {
                if (false && _index >= 0) {
                    System.out.println("BDD not freed! "+System.identityHashCode(this));
                }
                this.free();
            }
        }
        */
        
        /**
         * @see net.sf.javabdd.BDD#free()
         */
        @Override
		public void free() {
            bdd.deref(_index);
            _index = INVALID_BDD;
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#fullSatOne()
         */
        @Override
		public BDD fullSatOne() {
            throw new BDDException();
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#satOne(net.sf.javabdd.BDD, boolean)
         */
        @Override
		public BDD satOne(BDD var, boolean pol) {
            // TODO Implement this.
            throw new UnsupportedOperationException();
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#allsat()
         */
        @Override
		public List allsat() {
            throw new BDDException();
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#pathCount()
         */
        @Override
		public double pathCount() {
            throw new BDDException();
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDD#varProfile()
         */
        @Override
		public int[] varProfile() {
            throw new BDDException();
        }
        
    }

    private class bddPairing extends BDDPairing {
        
        private int[] from;
        private int[] to;
        private jdd.bdd.Permutation pairing;
        
        private bddPairing() {
            reset();
        }
        
        /* (non-Javadoc)
         * @see net.sf.javabdd.BDDPairing#set(int, int)
         */
        @Override
		public void set(int oldvar, int newvar) {
            for (int i = 0; i < from.length; ++i) {
                if (from[i] == vars[oldvar]) {
                    to[i] = vars[newvar];
                    pairing = bdd.createPermutation(from, to);
                    return;
                }
            }
            final int[] oldfrom = from;
            from = new int[from.length + 1];
            System.arraycopy(oldfrom, 0, from, 0, oldfrom.length);
            from[oldfrom.length] = vars[oldvar];
            final int[] oldto = to;
            to = new int[to.length + 1];
            System.arraycopy(oldto, 0, to, 0, oldto.length);
            to[oldto.length] = vars[newvar];
            pairing = bdd.createPermutation(from, to);
        }
        
        /* (non-Javadoc)
         * @see net.sf.javabdd.BDDPairing#set(int, net.sf.javabdd.BDD)
         */
        @Override
		public void set(int oldvar, BDD newvar) {
            throw new BDDException();
        }
        
        @Override
		public void set(int[] oldvar, int[] newvar) {
            final int[] oldfrom = from;
            from = new int[from.length + oldvar.length];
            System.arraycopy(oldfrom, 0, from, 0, oldfrom.length);
            for (int i = 0; i < oldvar.length; ++i) {
                from[i + oldfrom.length] = vars[oldvar[i]];
            }
            final int[] oldto = to;
            to = new int[to.length + newvar.length];
            System.arraycopy(oldto, 0, to, 0, oldto.length);
            for (int i = 0; i < newvar.length; ++i) {
                to[i + oldto.length] = vars[newvar[i]];
            }
            //debug();
            pairing = bdd.createPermutation(from, to);
        }
        
        void debug() {
            for (int i = 0; i < from.length; ++i) {
                System.out.println(bdd.getVar(from[i])+" -> "+bdd.getVar(to[i]));
            }
        }
        
        /* (non-Javadoc)
         * @see net.sf.javabdd.BDDPairing#reset()
         */
        @Override
		public void reset() {
            from = to = new int[] { };
            pairing = null;
        }
        
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#zero()
     */
    @Override
	public BDD zero() {
        return new bdd(bdd.getZero());
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#one()
     */
    @Override
	public BDD one() {
        return new bdd(bdd.getOne());
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#initialize(int, int)
     */
    @Override
	protected void initialize(int nodenum, int cachesize) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#isInitialized()
     */
    @Override
	public boolean isInitialized() {
        // TODO Auto-generated method stub
        return true;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#done()
     */
    @Override
	public void done() {
        bdd.cleanup();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setError(int)
     */
    @Override
	public void setError(int code) {
        // TODO Implement this.
    }
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#clearError()
     */
    @Override
	public void clearError() {
        // TODO Implement this.
    }
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setMaxNodeNum(int)
     */
    @Override
	public int setMaxNodeNum(int size) {
        // TODO Auto-generated method stub
        //throw new BDDException();
        return 0;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setMinFreeNodes(double)
     */
    @Override
	public double setMinFreeNodes(double x) {
        final int old = jdd.util.Configuration.minFreeNodesProcent;
        jdd.util.Configuration.minFreeNodesProcent = (int)(x * 100);
        return old / 100.;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setIncreaseFactor(double)
     */
    @Override
	public double setIncreaseFactor(double x) {
        // TODO.
        return 0.;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setMaxIncrease(int)
     */
    @Override
	public int setMaxIncrease(int x) {
        final int old = jdd.util.Configuration.maxNodeIncrease;
        jdd.util.Configuration.maxNodeIncrease = x;
        return old;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setNodeTableSize(int)
     */
    @Override
	public int setNodeTableSize(int x) {
        // TODO.
        return getNodeTableSize();
    }
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setCacheSize(int)
     */
    @Override
	public int setCacheSize(int x) {
        // TODO.
        return 0;
    }
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#getCacheSize()
     */
    @Override
	public int getCacheSize() {
        // TODO Implement this.
        throw new UnsupportedOperationException();
    }
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setCacheRatio(int)
     */
    @Override
	public double setCacheRatio(double x) {
        // TODO Auto-generated method stub
        return 0;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#varNum()
     */
    @Override
	public int varNum() {
        return bdd.numberOfVariables();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setVarNum(int)
     */
    @Override
	public int setVarNum(int num) {
        if (num > Integer.MAX_VALUE / 2) {
			throw new BDDException();
		}
        final int old = bdd.numberOfVariables();
        final int oldSize = vars.length;
        int newSize = oldSize;
        while (num > newSize) {
            newSize *= 2;
        }
        if (oldSize != newSize) {
            final int[] oldVars = vars;
            vars = new int[newSize];
            System.arraycopy(oldVars, 0, vars, 0, old);
            
            if (level2var != null) {
                final int[] oldlevel2var = level2var;
                level2var = new int[newSize];
                System.arraycopy(oldlevel2var, 0, level2var, 0, old);
                
                final int[] oldvar2level = var2level;
                var2level = new int[newSize];
                System.arraycopy(oldvar2level, 0, var2level, 0, old);
            }
        }
        while (bdd.numberOfVariables() < num) {
            final int k = bdd.numberOfVariables();
            vars[k] = bdd.createVar();
            bdd.ref(vars[k]);
            if (level2var != null) {
                level2var[k] = k;
                var2level[k] = k;
            }
        }
        return old;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#duplicateVar(int)
     */
    @Override
	public int duplicateVar(int var) {
        // TODO Implement this.
        throw new UnsupportedOperationException();
    }
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#ithVar(int)
     */
    @Override
	public BDD ithVar(int var) {
        if (var >= bdd.numberOfVariables()) {
			throw new BDDException();
		}
        //int v = var2level != null ? var2level[var] : var;
        final int v = var;
        return new bdd(vars[v]);
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#nithVar(int)
     */
    @Override
	public BDD nithVar(int var) {
        if (var >= bdd.numberOfVariables()) {
			throw new BDDException();
		}
        //int v = var2level != null ? var2level[var] : var;
        final int v = var;
        return new bdd(bdd.not(vars[v]));
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#printAll()
     */
    @Override
	public void printAll() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#printTable(net.sf.javabdd.BDD)
     */
    @Override
	public void printTable(BDD b) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#level2Var(int)
     */
    @Override
	public int level2Var(int level) {
        return level2var != null ? level2var[level] : level;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#var2Level(int)
     */
    @Override
	public int var2Level(int var) {
        return var2level != null ? var2level[var] : var;
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#reorder(net.sf.javabdd.BDDFactory.ReorderMethod)
     */
    @Override
	public void reorder(ReorderMethod m) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#autoReorder(net.sf.javabdd.BDDFactory.ReorderMethod)
     */
    @Override
	public void autoReorder(ReorderMethod method) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#autoReorder(net.sf.javabdd.BDDFactory.ReorderMethod, int)
     */
    @Override
	public void autoReorder(ReorderMethod method, int max) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#getReorderMethod()
     */
    @Override
	public ReorderMethod getReorderMethod() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#getReorderTimes()
     */
    @Override
	public int getReorderTimes() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#disableReorder()
     */
    @Override
	public void disableReorder() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#enableReorder()
     */
    @Override
	public void enableReorder() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#reorderVerbose(int)
     */
    @Override
	public int reorderVerbose(int v) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#setVarOrder(int[])
     */
    @Override
	public void setVarOrder(int[] neworder) {
        // todo: setting var order corrupts all existing BDD's!
        if (var2level != null) {
			throw new BDDException();
		}
        
        if (bdd.numberOfVariables() != neworder.length) {
			throw new BDDException();
		}
        
        final int[] newvars = new int[vars.length];
        var2level = new int[vars.length];
        level2var = new int[vars.length];
        for (int i = 0; i < bdd.numberOfVariables(); ++i) {
            final int k = neworder[i];
            //System.out.println("Var "+k+" (node "+vars[k]+") in original order -> var "+i+" (node "+vars[i]+") in new order");
            newvars[k] = vars[i];
            var2level[k] = i;
            level2var[i] = k;
        }
        vars = newvars;
        
        //System.out.println("Number of domains: "+numberOfDomains());
        for (int i = 0; i < numberOfDomains(); ++i) {
            final BDDDomain d = getDomain(i);
            d.var = makeSet(d.ivar);
            //System.out.println("Set for domain "+d+": "+d.var.toStringWithDomains());
        }
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#addVarBlock(net.sf.javabdd.BDD, boolean)
     */
    @Override
	public void addVarBlock(BDD var, boolean fixed) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#addVarBlock(int, int, boolean)
     */
    @Override
	public void addVarBlock(int first, int last, boolean fixed) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#varBlockAll()
     */
    @Override
	public void varBlockAll() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#clearVarBlocks()
     */
    @Override
	public void clearVarBlocks() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#printOrder()
     */
    @Override
	public void printOrder() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#nodeCount(java.util.Collection)
     */
    @Override
	public int nodeCount(Collection r) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#getNodeTableSize()
     */
    @Override
	public int getNodeTableSize() {
        // todo.
        return bdd.countRootNodes();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#getNodeNum()
     */
    @Override
	public int getNodeNum() {
        // todo.
        return bdd.countRootNodes();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#reorderGain()
     */
    @Override
	public int reorderGain() {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#printStat()
     */
    @Override
	public void printStat() {
        bdd.showStats();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#makePair()
     */
    @Override
	public BDDPairing makePair() {
        return new bddPairing();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#swapVar(int, int)
     */
    @Override
	public void swapVar(int v1, int v2) {
        throw new BDDException();
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#createDomain(int, BigInteger)
     */
    @Override
	protected BDDDomain createDomain(int a, BigInteger b) {
        return new bddDomain(a, b);
    }

    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#createBitVector(int)
     */
    @Override
	protected BDDBitVector createBitVector(int a) {
        return new bddBitVector(a);
    }
    
    private class bddDomain extends BDDDomain {

        private bddDomain(int a, BigInteger b) {
            super(a, b);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDDBitVector#getFactory()
         */
        @Override
		public BDDFactory getFactory() { return JDDFactory.this; }

    }
    
    private class bddBitVector extends BDDBitVector {

        private bddBitVector(int a) {
            super(a);
        }

        /* (non-Javadoc)
         * @see net.sf.javabdd.BDDBitVector#getFactory()
         */
        @Override
		public BDDFactory getFactory() { return JDDFactory.this; }

    }
    
    public static final String REVISION = "$Revision: 1.5 $";
    
    /* (non-Javadoc)
     * @see net.sf.javabdd.BDDFactory#getVersion()
     */
    @Override
	public String getVersion() {
        return "JDD "+REVISION.substring(11, REVISION.length()-2);
    }
}
