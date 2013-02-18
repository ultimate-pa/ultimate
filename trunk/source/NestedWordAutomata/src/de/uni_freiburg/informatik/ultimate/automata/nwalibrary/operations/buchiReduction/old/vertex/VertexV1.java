/**
 * Vertex for fair, direct and ordinary simulation.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.old.vertex;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 10.12.2011
 */
public class VertexV1<LETTER,STATE> extends Vertex<LETTER, STATE> {
    /*_______________________________________________________________________*\
    \* FIELDS / ATTRIBUTES                                                   */
    
    /**
     * The priority of this vertex.
     * TODO : byte would be enough!
     */
    private int priority;
    /**
     * The progressMeasure for Jurdzinski lifting function.
     */
    private int pm;
    /**
     * The b required for the efficient lifting algorithm implementation.
     */
    private int b_eff;
    /**
     * The c required for the efficient lifting algorithm implementation.
     */
    private int c;

    /*_______________________________________________________________________*\
    \* CONSTRUCTORS                                                          */
    
    /**
     * Constructor.
     * 
     * @param priority
     *            the priority of this vertex
     * @param q0
     *            the label of the first Buchi automaton state
     * @param q1
     *            the label of the second Buchi automaton state
     */
    public VertexV1(int priority, STATE q0, STATE q1) {
    	super(q0, q1);
        this.priority = priority;
        // int initializes to zero anyway ...
        // this.progressMeasure = 0;
        // this.b = 0;
        // this.c = 0;
    }

    /*_______________________________________________________________________*\
    \* METHODS                                                               */
    
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<(").append(getQ0()).append(",").append(getQ1());
        sb.append("),p:").append(getPriority()).append(",pm:");
        sb.append(getPM()).append(">");
        return sb.toString();
    }
    
    /*_______________________________________________________________________*\
    \* GETTERS AND SETTERS                                                     */
    
    /**
     * Getter for the priority of this vertex.
     * 
     * @return the priority
     */
    public int getPriority() {
        return priority;
    }
    
    /**
     * Getter for ProgressMeasure.
     * 
     * @return the progress measure
     */
    public int getPM() {
        return pm;
    }

    /**
     * Setter for ProgressMeasure.
     * 
     * @param pm
     *            the progress measure
     */
    public void setPM(int pm) {
        this.pm = pm;
    }

	/**
	 * Getter for b.
	 * @return the b
	 */
	public int getBEff() {
		return b_eff;
	}

	/**
	 * Setter for b.
	 * @param b the b to set
	 */
	public void setBEff(int b) {
		this.b_eff = b;
	}

	/**
	 * Getter for c.
	 * @return the c
	 */
	public int getC() {
		return c;
	}

	/**
	 * Setter for c.
	 * @param c the c to set
	 */
	public void setC(int c) {
		this.c = c;
	}
}
