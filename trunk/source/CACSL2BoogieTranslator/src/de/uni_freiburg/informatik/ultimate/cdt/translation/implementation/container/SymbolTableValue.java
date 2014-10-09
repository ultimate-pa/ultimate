/**
 * Container to hold the value part in the symbol table. I.e. the Boogie
 * name and the C Declaration and whether the variable is global or not.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;

/**
 * @author Markus Lindenmann
 * @date 13.07.2012
 */
public class SymbolTableValue {
	
	/**
	 * Enum representing the C storageclass (e.g. typedef,..) of the SymbolTableValue
	 * @author alex
	 */
	public static enum StorageClass {
		AUTO, EXTERN, /*LAST,*/ MUTABLE, REGISTER, STATIC, TYPEDEF, UNSPECIFIED
	}
	
    /**
     * The variable name in the Boogie program.
     */
    private final String boogieName;
    
    /**
     * the C-style declaration of the symbol
     */
    private final CDeclaration cDecl;
    
    /**
     * The variable declaration in the Boogie program.
     */
    private final Declaration boogieDecl;
    /**
     * Whether the variable is a global variable in the C program or not.
     */
    private final boolean isGlobalVar;
    
    /**
     * the storageClass of this symbol
     */
    StorageClass storageClass;
    
    
    public boolean isIntFromPointer;
    
    /**
     * The description of the C variable.
     */
//    private final CType cvar;
    
//    /**
//     * True iff this C variable has static storage class.
//     */
//    private final boolean isStatic;

    /**
     * Constructor.
     * 
     * @param bId
     *            Boogie identifier.
     * @param cdecl
     *            Boogie variable declaration.
     * @param isGlobal
     *            whether the variable is a global variable in the C program or
     *            not.
     * @param cvar
     *            a description of the C variable.
     * @param isStatic
     *            whether the variable is static in the C program or not
     */
    public SymbolTableValue(String bId, Declaration boogieDecl, CDeclaration cdecl,
            boolean isGlobal, StorageClass sc) {
//            , boolean isStatic) {
        assert bId != null && !bId.equals(SFO.EMPTY);
        this.boogieName = bId;
        assert cdecl != null;
        this.cDecl = cdecl;
        this.boogieDecl = boogieDecl;
        this.isGlobalVar = isGlobal;
        this.storageClass = sc;
//        this.cvar = cvar;
//        this.isStatic = isStatic;
    }

    /**
     * Return the Boogie variable name.
     * 
     * @return the boogieName
     */
    public String getBoogieName() {
        return boogieName;
    }

    /**
     * Return the Boogie variable declaration.
     * 
     * @return the decl
     */
    public CDeclaration getCDecl() {
        return cDecl;
    }
    
    public Declaration getBoogieDecl() {
        return boogieDecl;
    }
    /**
     * Return whether the variable is global in the boogie program or not.
     * (for instance static C variables are global boogie variables for us)
     * 
     * @return the isGlobalVar
     */
    public boolean isBoogieGlobalVar() {
        return isGlobalVar;
    }

    /**
     * Getter for the C variable description.
     * 
     * @return the C variable description.
     */
    public CType getCVariable() {
        return this.cDecl.getType();
    }
    
    public boolean isStatic() {
    	return this.storageClass == StorageClass.STATIC;
    }
}
