/**
 * Vertex for fair bi-simulation.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.old.vertex;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 16.12.2011
 */
public class VertexV0FairBisimulation<LETTER,STATE> extends VertexV0Delayed<LETTER, STATE> {
    /*_______________________________________________________________________*\
    \* FIELDS / ATTRIBUTES                                                   */
    
    /**
     * The extra bit b2.
     */
    private boolean b2;

    /*_______________________________________________________________________*\
    \* CONSTRUCTORS                                                          */
    
    /**
     * Vertex constructor.
     * 
     * @param priority
     *            the priority of this vertex
     * @param b1
     *            the extra bit b1
     * @param b2
     *            the extra bit b2
     * @param q0
     *            the label of the first Buchi automaton state
     * @param q1
     *            the label of the second Buchi automaton state
     * @param a
     *            the label of the Buchi automaton edge
     */
    public VertexV0FairBisimulation(int priority, boolean b1, boolean b2, STATE q0,
            STATE q1, LETTER a) {
        super(priority, b1, q0, q1, a);
        this.setB2(b2);
    }
    
    /**
     * Vertex constructor.
     * 
     * @param copy
     *            the Vertex to copy
     */
    public VertexV0FairBisimulation(VertexV0FairBisimulation<LETTER,STATE> copy) {
        this(copy.getPriority(), copy.isB1(), copy.isB2(), copy.getQ0(), copy
                .getQ1(), copy.getA());
    }

    /*_______________________________________________________________________*\
    \* METHODS                                                               */
    
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<").append(isB1()).append(",").append(isB2()).append(",(");
        sb.append(getQ0()).append(",").append(getQ1()).append("),p:");
        sb.append(getPriority()).append(",pm:").append(getPM());
        sb.append(">");
        return sb.toString();
    }
    
    /*_______________________________________________________________________*\
    \* GETTERS AND SETTERS                                                   */
    
    /**
     * Getter for the extra bit b1.
     * 
     * @return the b1
     */
    public boolean isB1() {
        // just to make the interface intuitive!
        return super.isB();
    }

    /**
     * Getter for the extra bit b2.
     * 
     * @return the b2
     */
    public boolean isB2() {
        return b2;
    }

    /**
     * Setter for the extra bit b2.
     * 
     * @param b2
     *            the b2 to set
     */
    public void setB2(boolean b2) {
        this.b2 = b2;
    }
    
    /**
     * Returns q0 if stateNumber == false, q1 otherwise
     * 
     * @param stateNumber
     *            number of state to return.
     * @return state
     */
    public STATE getQ(boolean stateNumber) {
        if (stateNumber)
            return getQ1();
        else
            return getQ0();
    }
}
