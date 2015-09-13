/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
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
public class TypesResult extends Result {

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
    public TypesResult(ASTType node, boolean isConst, boolean isVoid,
            CType cvar) {
        super(node);
        this.isConst = isConst;
        this.isVoid = isVoid;
        this.typeDeclarations = new ArrayList<TypeDeclaration>();
        this.cType = cvar;
    }

    public TypesResult(TypesResult copy) {
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
