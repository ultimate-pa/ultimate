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
 * Symbol Table for the compiler. 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.cdt.parser.MultiparseSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @author Markus Lindenmann
 * @since 13.07.2012
 */
public class SymbolTable extends LinkedScopedHashMap<String, SymbolTableValue> {
    /**
     * Holds a map from BoogieIDs and the corresponding CIDs.
     */
    private final HashMap<String, String> boogieID2CID;
    

    private final HashMap<CDeclaration, Declaration> mCDecl2BoogieDecl;
    /**
     * unique ID for current scope.
     */
    private int compoundCounter;

    private final Stack<Integer> compoundNrStack = new Stack<>();;
    
    private final MultiparseSymbolTable mMultiparseInformation;

    /**
     * A reference to the main dispatcher.
     */
    private final Dispatcher main;

    @Override
    public SymbolTableValue put(String cId, SymbolTableValue value) {
        if (!main.mTypeHandler.isStructDeclaration()) {
            final SymbolTableValue v = super.put(cId, value);
            boogieID2CID.put(value.getBoogieName(), cId);
            mCDecl2BoogieDecl.put(value.getCDecl(), value.getBoogieDecl());
            return v;
        }
        return null;
    }

    /**
     * @Override
     * @deprecated ignores the error location! Use
     *             <code>get(String, Location)</code> instead.
     **/
    @Deprecated
	@Override
	public SymbolTableValue get(Object cId) {
        return get((String) cId, null);
    }

    /**
     * Returns the SymbolTableValue for the id cId.
     * 
     * @param cId
     *            the C identifier.
     * @param errorLoc
     *            the location for possible errors.
     * @return the corresponding symbol table value.
     */
    public SymbolTableValue get(final String cId, final ILocation errorLoc) {
        if (!(cId instanceof String)) {
            throw new IllegalArgumentException(
                    "Not a valid key for symbol table: " + cId.getClass());
        }
        if (!containsKey(cId)) {
            final String msg = "Variable is neither declared globally nor locally! ID="
                    + cId;
            throw new IncorrectSyntaxException(errorLoc, msg);
        }
        return super.get(cId);
    }


    @Override
    public void beginScope() {
        super.beginScope();
        compoundCounter++;
        compoundNrStack.push(compoundCounter);
    }

    @Override
    public void endScope() {
        super.endScope();
        compoundNrStack.pop();
    }

    /**
     * Whether the specified C variable is in the table.
     * 
     * @param cId
     *            the C identifier.
     * @return true iff contained.
     */
    public boolean containsCSymbol(String cId) {
        return containsKey(cId);
    }

    /**
     * Whether the specified Boogie variable is in the table.
     * 
     * @param boogieId
     *            the C identifier.
     * @return true iff contained.
     */
    public boolean containsBoogieSymbol(String boogieId) {
        return boogieID2CID.containsKey(boogieId);
    }

    /**
     * Constructor.
     * 
     * @param main
     *            a reference to the main dispatcher.
     */
    public SymbolTable(Dispatcher main, final MultiparseSymbolTable mst) {
        super();
        boogieID2CID = new HashMap<String, String>();
        mCDecl2BoogieDecl = new HashMap<CDeclaration, Declaration>();
        compoundCounter = 0;
        this.main = main;
        mMultiparseInformation = mst;
    }

    /**
     * Adds an entry into the map to translate Boogie to C identifiers. <br/>
     * Consider using <code>put()</code>
     * 
     * @param boogieIdentifier
     *            the Boogie identifier.
     * @param loc
     *            where to report errors to?
     * @param cIdentifier
     *            the C identifier.
     */
    public void addToReverseMap(String boogieIdentifier, String cIdentifier,
            ILocation loc) {
        final String old = boogieID2CID.put(boogieIdentifier, cIdentifier);
        if (old != null && !old.equals(cIdentifier)) {
            final String msg = "Variable with this name was already declared before:"
                    + cIdentifier;
            throw new IncorrectSyntaxException(loc, msg);
        }
    }

    /**
     * Get the C identifier for a Boogie identifier.
     * 
     * @param boogieIdentifier
     *            the Boogie identifier.
     * @param loc
     *            where to report errors to?
     * @return the C identifier.
     */
    public String getCID4BoogieID(String boogieIdentifier, ILocation loc) {
        if (!boogieID2CID.containsKey(boogieIdentifier)) {
            final String msg = "Variable not found: " + boogieIdentifier;
            throw new IncorrectSyntaxException(loc, msg);
        }
        return boogieID2CID.get(boogieIdentifier);
    }

    /**
     * returns a unique number for each scope!
     * 
     * @return a unique number for the current scope.
     */
    public int getCompoundCounter() {
    	if (compoundNrStack.isEmpty()) {
			return 0;
		} else {
			return compoundNrStack.peek();
		}
    }

    /**
     * Checks the symbol table for the given C identifier. Iff it is contained,
     * the ASTType of this variable in the current scope is returned.
     * 
     * @param cId
     *            the C identifier, to look for.
     * @param loc
     *            the location for errors / warnings.
     * @return the found ASTType.
     */
    public ASTType getTypeOfVariable(String cId, ILocation loc) {
    	return main.mTypeHandler.cType2AstType(loc, this.get(cId, loc).getCVariable());
//        if (this.get(cId, loc).getBoogieDecl() instanceof VariableDeclaration) {
//            VariableDeclaration vd = (VariableDeclaration) get(cId, loc)
//                    .getBoogieDecl();
//            // on index 0, because the type is the same for all ...
//            return vd.getVariables()[0].getType(); //FIXME ??
//        } else if (this.get(cId, loc).getBoogieDecl() instanceof ConstDeclaration) {
//            ConstDeclaration cd = (ConstDeclaration) get(cId, loc).getBoogieDecl();
//            return cd.getVarList().getType();
//        } else {
//            String msg = "Unexpected declaration in symbol table!";
//            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
//            throw new UnsupportedSyntaxException(msg);
//        }
    }
    
    public Declaration getBoogieDeclOfCDecl(CDeclaration cDec) {
    	return mCDecl2BoogieDecl.get(cDec);
    }

    /**
     * Getter for boogieID2CID map.
     * 
     * @return a map from boogie IDs to C IDs.
     */
    public Map<String, String> getIdentifierMapping() {
        return Collections.unmodifiableMap(boogieID2CID);
    }

	public boolean existsInCurrentScope(String name) {
		if (!containsCSymbol(name)) {
			return false;
		}
		boolean result = false;
		for (final String k : currentScopeKeys()) {
			result |= name.equals(k);
		}
		return result;
	}
}
