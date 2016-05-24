/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Container to hold the value part in the symbol table. I.e. the Boogie
 * name and the C Declaration and whether the variable is global or not.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

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
    
//    /**
//     * the storageClass of this symbol
//     */
//    StorageClass storageClass;
    
    
    public boolean isIntFromPointer;
    
    /**
     * The description of the C variable.
     */
//    private final CType cvar;
    
//    /**
//     * True iff this C variable has static storage class.
//     */
//    private final boolean isStatic;
    
    private final IASTNode mDeclarationNode;

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
//            boolean isGlobal, StorageClass sc, IASTNode declNode) {
            boolean isGlobal, IASTNode declNode) {
//            , boolean isStatic) {
        assert bId != null && !bId.equals(SFO.EMPTY);
        this.boogieName = bId;
        assert cdecl != null;
        this.cDecl = cdecl;
        this.boogieDecl = boogieDecl;
        this.isGlobalVar = isGlobal;
//        this.storageClass = sc;
//        this.cvar = cvar;
//        this.isStatic = isStatic;
        mDeclarationNode = declNode;
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
    
//    public boolean isStatic() {
//    	return this.storageClass == StorageClass.STATIC;
//    }
//
//    public boolean isExtern() {
//    	return this.storageClass == StorageClass.EXTERN;
//    }

	public IASTNode getDeclarationNode() {
		return mDeclarationNode;
	}
    
    
}
