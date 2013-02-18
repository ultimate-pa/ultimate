/**
 * Vertex for delayed simulation and fair bi-simulation.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.old.vertex;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 16.12.2011
 */
public class VertexV1Delayed<LETTER,STATE> extends VertexV1<LETTER, STATE> {
    /*_______________________________________________________________________*\
    \* FIELDS / ATTRIBUTES                                                   */
    
    /**
     * The extra bit b.
     */
    private boolean b;

    /*_______________________________________________________________________*\
    \* CONSTRUCTORS                                                          */
    
    /**
     * Vertex constructor.
     * 
     * @param priority
     *            the priority of this vertex
     * @param b
     *            the extra bit b
     * @param q0
     *            the label of the first Buchi automaton state
     * @param q1
     *            the label of the second Buchi automaton state
     */
    public VertexV1Delayed(int priority, boolean b, STATE q0, STATE q1) {
        super(priority, q0, q1);
        this.b = b;
    }

    /*_______________________________________________________________________*\
    \* METHODS                                                               */
    
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<").append(isB()).append(",(").append(getQ0()).append(",");
        sb.append(getQ1()).append("),p:").append(getPriority()).append(",pm:")
                .append(getPM()).append(">");
        return sb.toString();
    }
    
    /*_______________________________________________________________________*\
    \* GETTERS AND SETTERS                                                   */
    
    /**
     * Getter for the extra bit b.
     * 
     * @return the b
     */
    public boolean isB() {
        return b;
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
