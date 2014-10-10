/**
 * Location in a C+ACSL program.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.io.Serializable;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 06.03.2012
 */
public class CACSLLocation implements Serializable, ILocation {
    /**
     * Serial version UID.
     */
    private static final long serialVersionUID = -194821240021400957L;
    /**
     * The translated IAST node.
     */
    protected final IASTNode cNode;
    /**
     * The translated IAST node.
     */
    protected final ACSLNode acslNode;
    /**
     * The m_CheckedSpecification of check/assertion applied to this node.
     */
    protected Check m_CheckedSpecification;

    /**
     * Constructor.
     * 
     * @param cNode
     *            the corresponding C AST node.
     */
    public CACSLLocation(IASTNode cNode) {
        this(cNode, new Check(Check.Spec.UNKNOWN));
    }

    /**
     * Constructor.
     * 
     * @param acslNode
     *            the corresponding C AST node.
     */
    public CACSLLocation(ACSLNode acslNode) {
        this(acslNode, new Check(Check.Spec.UNKNOWN));
    }

    /**
     * Constructor.
     * 
     * @param cNode
     *            the corresponding C AST node.
     * @param type
     *            the type of check/assertion
     */
    public CACSLLocation(IASTNode cNode, Check type) {
        this.cNode = cNode;
        this.acslNode = null;
        this.m_CheckedSpecification = type;
    }

    /**
     * Constructor.
     * 
     * @param acslNode
     *            the corresponding C AST node.
     * @param type
     *            the type of check/assertion
     */
    public CACSLLocation(ACSLNode acslNode, Check type) {
        this.acslNode = acslNode;
        this.cNode = null;
        this.m_CheckedSpecification = type;
    }

    /**
     * Copy Constructor.
     * 
     * @param loc
     *            the location to copy.
     * @param type
     *            the new type to set.
     */
    public CACSLLocation(CACSLLocation loc, Check type) {
        this(loc);
        this.m_CheckedSpecification = type;
    }
    
    /**
     * Copy Constructor.
     * 
     * @param loc
     *            the location to copy.
     */
    public CACSLLocation(CACSLLocation loc) {
        this.acslNode = loc.acslNode;
        this.cNode = loc.cNode;
        this.m_CheckedSpecification = loc.m_CheckedSpecification;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (cNode != null && acslNode != null) {
            sb.append("Mixed Node: ");
        }
        if (cNode != null) {
            sb.append("C: ");
            sb.append(cNode.getRawSignature());
            sb.append(" ");
        }
        if (acslNode != null) {
            sb.append("ACSL: ");
            sb.append(acslNode.toString());
        }

        return sb.toString();
        // return getStartLine() + "/" + getStartColumn()
        // + "-" + getEndLine() + "/" + getEndColumn();
    }

    @Override
    public int getStartLine() {
        if (cNode != null) {
            return cNode.getFileLocation().getStartingLineNumber();
        }
        if (acslNode != null) {
            return acslNode.getStartingLineNumber();
        }
        throw new IllegalArgumentException("One node was null!");
    }

    @Override
    public int getEndLine() {
        if (cNode != null) {
            return cNode.getFileLocation().getEndingLineNumber();
        }
        if (acslNode != null) {
            return acslNode.getEndingLineNumber();
        }
        throw new IllegalArgumentException("One node was null!");
    }

    @Override
    public int getStartColumn() {
        return -1;
    }

    @Override
    public int getEndColumn() {
        return -1;
    }

    @Override
    public String getFileName() {
        if (cNode != null) {
            return cNode.getFileLocation().getFileName();
        }
        if (acslNode != null) {
            return acslNode.getFileName();
        }
        throw new IllegalArgumentException("One node was null!");
    }

    @Override
    public ILocation getOrigin() {
        return this;
    }

    @Override
    public Check checkedSpecification() {
    	return m_CheckedSpecification;
    }

    /**
     * @return the cNode
     */
    public IASTNode getCNode() {
        return cNode;
    }

    /**
     * @return the acslNode
     */
    public ACSLNode getAcslNode() {
        return acslNode;
    }

    @Override
    public boolean isLoop() {
        return false;
    }
}