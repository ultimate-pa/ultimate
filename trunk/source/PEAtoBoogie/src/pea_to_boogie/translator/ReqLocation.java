/**
 * Location in a C+ACSL program.
 */
package pea_to_boogie.translator;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * @author Jochen Hoenicke
 * @date 06.03.2012
 */
public class ReqLocation implements Serializable, ILocation {
    /**
     * Serial version UID.
     */
    private static final long serialVersionUID = -194821240021400957L;
    /**
     * The m_CheckedSpecification of check/assertion applied to this node.
     */
    protected ReqCheck m_CheckedSpecification;

    /**
     * Constructor.
     * 
     * @param cNode
     *            the corresponding C AST node.
     * @param type
     *            the type of check/assertion
     */
    public ReqLocation(ReqCheck checkNode) {
        this.m_CheckedSpecification = checkNode;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
    	return m_CheckedSpecification.toString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getStartLine()
     */
    @Override
    public int getStartLine() {
    	return m_CheckedSpecification.getStartLine();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getEndLine()
     */
    @Override
    public int getEndLine() {
    	return m_CheckedSpecification.getEndLine();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getStartColumn()
     */
    @Override
    public int getStartColumn() {
        return -1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getEndColumn()
     */
    @Override
    public int getEndColumn() {
        return -1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getFileName()
     */
    @Override
    public String getFileName() {
    	return m_CheckedSpecification.getFileName();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getOrigin()
     */
    @Override
    public ILocation getOrigin() {
        return this;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uni_freiburg.informatik.ultimate.model.Location#checkedSpecification()
     */
    @Override
    public Check getCheck() {
    	return m_CheckedSpecification;
    }

    @Override
    public boolean isLoop() {
        return false;
    }
}