/**
 * A Result node holding a some stuff for a type.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 09.02.2012
 */
public class ResultTypes extends Result {

    /**
     * We need this flag to determine, if this declaration is a constant or not.
     */
    public final boolean isConst;
    /**
     * Whether the type is void, which is not directly representable in Boogie.
     */
    public final boolean isVoid;
    /**
     * A list of type declarations.
     */
    public final ArrayList<TypeDeclaration> typeDeclarations;
    /**
     * C variable description.
     */
    public CType cType;
    
    /**
     * Flag describing whether the Boogie variable that is declared according to the
     * declarator that this ResultTypes is generated from should be stored on the heap
     * (bc it is addressoffed later) or not.
     */
    public boolean isOnHeap = false;

    /**
     * Constructor.
     * 
     * @param node
     *            the BoogieASTNode to hold.
     * @param isConst
     *            boolean flag to determine constant.
     * @param isVoid
     *            boolean flag to determine void.
     * @param cvar
     *            a description of the C variable.
     */
    public ResultTypes(ASTType node, boolean isConst, boolean isVoid,
            CType cvar) {
        super(node);
        this.isConst = isConst;
        this.isVoid = isVoid;
        this.typeDeclarations = new ArrayList<TypeDeclaration>();
        this.cType = cvar;
    }

    public ResultTypes(ResultTypes copy) {
        super(copy.node);
        this.isConst = copy.isConst;
        this.isVoid = copy.isVoid;
        this.typeDeclarations = new ArrayList<TypeDeclaration>(copy.typeDeclarations);
        this.cType = copy.cType;
        this.isOnHeap = copy.isOnHeap;
    }
    /**
     * Getter for the type.
     * 
     * @return the type.
     */
    public ASTType getType() {
        return (ASTType) super.node;
    }

    /**
     * Adds a list of type declarations to this result.
     * 
     * @param tds
     *            a list of type declarations.
     */
    public void addTypeDeclarations(ArrayList<TypeDeclaration> tds) {
        this.typeDeclarations.addAll(tds);
    }
    
    @Override
    public String toString() {
    	return "ResultTypes: " + cType;
    }
}
