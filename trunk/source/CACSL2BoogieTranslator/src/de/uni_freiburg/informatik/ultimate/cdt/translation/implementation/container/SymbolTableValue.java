/**
 * Container to hold the value part in the symbol table. I.e. the Boogie
 * name and the C Declaration and whether the variable is global or not.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;

/**
 * @author Markus Lindenmann
 * @date 13.07.2012
 */
public class SymbolTableValue {
    /**
     * The variable name in the Boogie program.
     */
    private final String boogieName;
    /**
     * The variable declaration in the Boogie program.
     */
    private final Declaration decl;
    /**
     * Whether the variable is a global variable in the C program or not.
     */
    private final boolean isGlobalVar;
    /**
     * The description of the C variable.
     */
    private final CType cvar;

    /**
     * Constructor.
     * 
     * @param bId
     *            Boogie identifier.
     * @param decl
     *            Boogie variable declaration.
     * @param isGlobal
     *            whether the variable is a global variable in the C program or
     *            not.
     * @param cvar
     *            a description of the C variable.
     */
    public SymbolTableValue(String bId, Declaration decl,
            boolean isGlobal, CType cvar) {
        assert bId != null && !bId.equals(SFO.EMPTY);
        this.boogieName = bId;
        assert decl != null;
        this.decl = decl;
        this.isGlobalVar = isGlobal;
        this.cvar = cvar;
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
    public Declaration getDecl() {
        return decl;
    }

    /**
     * Return whether the variable is global in the C program or not.
     * 
     * @return the isGlobalVar
     */
    public boolean isGlobalVar() {
        return isGlobalVar;
    }

    /**
     * Getter for the C variable description.
     * 
     * @return the C variable description.
     */
    public CType getCVariable() {
        return this.cvar;
    }
}
