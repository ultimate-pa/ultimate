/**
 * Vertex for delayed simulation.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.old.vertex;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 16.12.2011
 */
public class VertexV0Delayed<LETTER,STATE> extends VertexV0<LETTER, STATE> {
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
     * @param a
     *            the label of the Buchi automaton edge
     */
    public VertexV0Delayed(int priority, boolean b, STATE q0, STATE q1, LETTER a) {
        super(priority, q0, q1, a);
        this.b = b;
    }

    /*_______________________________________________________________________*\
    \* METHODS                                                               */
    
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<").append(b).append(",(").append(getQ0()).append(",");
        sb.append(getQ1()).append(",").append(getA()).append("),p:");
        sb.append(getPriority()).append(",pm:").append(getPM());
        sb.append(">");
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
     * Setter for the extra bit b.
     * 
     * @param b
     *            the b to set
     */
    protected void setB(boolean b) {
        this.b = b;
    }
}
