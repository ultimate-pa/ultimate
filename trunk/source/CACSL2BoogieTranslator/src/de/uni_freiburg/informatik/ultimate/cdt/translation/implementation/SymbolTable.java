/**
 * Symbol Table for the compiler. 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * @author Markus Lindenmann
 * @since 13.07.2012
 */
public class SymbolTable extends ScopedHashMap<String, SymbolTableValue> {
    /**
     * Holds a map from BoogieIDs and the corresponding CIDs.
     */
    private HashMap<String, String> boogieID2CID;
    /**
     * unique ID for current scope.
     */
    private int compoundCounter;
    /**
     * A reference to the main dispatcher.
     */
    private Dispatcher main;

    @Override
    public SymbolTableValue put(String cId, SymbolTableValue value) {
        if (!main.typeHandler.isStructDeclaration()) {
            SymbolTableValue v = super.put(cId, value);
            boogieID2CID.put(value.getBoogieName(), cId);
            return v;
        }
        return null;
    }

    /**
     * @Override
     * @deprecated ignores the error location! Use
     *             <code>get(String, Location)</code> instead.
     **/
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
            String msg = "Variable is neither declared globally nor locally! ID="
                    + cId;
            Dispatcher.error(errorLoc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        return super.get(cId);
    }

    @Override
    public void beginScope() {
        super.beginScope();
        compoundCounter++;
    }

    /**
     * Whether the specified C variable is in the table.
     * 
     * @param cId
     *            the C identifier.
     * @return true iff contained.
     */
    public boolean containsCSymbol(String cId) {
        return this.containsKey(cId);
    }

    /**
     * Whether the specified Boogie variable is in the table.
     * 
     * @param boogieId
     *            the C identifier.
     * @return true iff contained.
     */
    public boolean containsBoogieSymbol(String boogieId) {
        return this.boogieID2CID.containsKey(boogieId);
    }

    /**
     * Constructor.
     * 
     * @param main
     *            a reference to the main dispatcher.
     */
    public SymbolTable(Dispatcher main) {
        super();
        this.boogieID2CID = new HashMap<String, String>();
        this.compoundCounter = 0;
        this.main = main;
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
        String old = boogieID2CID.put(boogieIdentifier, cIdentifier);
        if (old != null && !old.equals(cIdentifier)) {
            String msg = "Variable with this name was already declared before:"
                    + cIdentifier;
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
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
            String msg = "Variable not found: " + boogieIdentifier;
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        return boogieID2CID.get(boogieIdentifier);
    }

    /**
     * returns a unique number for each scope!
     * 
     * @return a unique number for the current scope.
     */
    public int getCompoundCounter() {
        return compoundCounter;
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
        if (get(cId, loc).getDecl() instanceof VariableDeclaration) {
            VariableDeclaration vd = (VariableDeclaration) get(cId, loc)
                    .getDecl();
            // on index 0, because the type is the same for all ...
            return vd.getVariables()[0].getType();
        } else if (get(cId, loc).getDecl() instanceof ConstDeclaration) {
            ConstDeclaration cd = (ConstDeclaration) get(cId, loc).getDecl();
            // on index 0, because the type is the same for all ...
            return cd.getVarList().getType();
        } else {
            String msg = "Unexpected declaration in symbol table!";
            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
            throw new UnsupportedSyntaxException(msg);
        }
    }

    /**
     * Getter for boogieID2CID map.
     * 
     * @return a map from boogie IDs to C IDs.
     */
    public Map<String, String> getIdentifierMapping() {
        return Collections.unmodifiableMap(boogieID2CID);
    }
}