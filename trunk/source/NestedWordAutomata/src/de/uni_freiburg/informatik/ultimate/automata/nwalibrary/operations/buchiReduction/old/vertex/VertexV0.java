/**
 * Vertex for fair, direct and ordinary simulation.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.old.vertex;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 10.12.2011
 */
public class VertexV0<LETTER,STATE> extends VertexV1<LETTER, STATE> {
    /*_______________________________________________________________________*\
    \* FIELDS / ATTRIBUTES                                                   */
    
    /**
     * The label of the edge in the Buchi automaton.
     */
    private LETTER a;

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
     * @param a
     *            the label of the Buchi automaton edge
     */
    public VertexV0(int priority, STATE q0, STATE q1, LETTER a) {
        super(priority, q0, q1);
        this.a = a;
    }

    /*_______________________________________________________________________*\
    \* METHODS                                                               */
    
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<(").append(getQ0()).append(",").append(getQ1());
        sb.append(",").append(getA()).append("),p:").append(getPriority());
        sb.append(",pm:").append(getPM()).append(">");
        return sb.toString();
    }
    
    /*_______________________________________________________________________*\
    \* GETTERS AND SETTERS                                                   */
    
    /**
     * Getter for the label of the Buchi automaton edge.
     * 
     * @return the label
     */
    public LETTER getA() {
        return a;
    }
}
