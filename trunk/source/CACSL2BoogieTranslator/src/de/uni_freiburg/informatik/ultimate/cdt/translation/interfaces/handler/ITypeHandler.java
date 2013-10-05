/**
 * Describes a Type Handler.
 * It basically treats all sub-interfaces which derive from IASTDeclSpecifier.
 * We do not treat especially the main interface because only the sub-interfaces,
 * are interesting for us.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler;

import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IBasicType;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.02.2012
 */
public interface ITypeHandler extends IHandler {

    /**
     * Whether the current declaration is a struct declaration.
     * 
     * @return true, iff struct field declarations are dispatched.
     */
    public boolean isStructDeclaration();

    /**
     * Translates an IASTSimpleDeclSpecifier. Basically treats all the build in
     * types of C
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTSimpleDeclSpecifier node);

    /**
     * Translates an IASTNamedTypeSpecifier.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTNamedTypeSpecifier node);

    /**
     * Translates an IASTEnumerationSpecifier.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTEnumerationSpecifier node);

    /**
     * Translates an IASTElaboratedTypeSpecifier.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTElaboratedTypeSpecifier node);

    /**
     * Translates an IASTCompositeTypeSpecifier.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTCompositeTypeSpecifier node);

    /**
     * Type handling for int vs bool, since bools are integers in C99 -> we have
     * to translate this special case into BooleanLiterals. If we are in a
     * boolean context, all int != 0 are true, else false.
     * 
     * @param expr
     *            the expression to assign
     * @param loc
     *            the CACSLLocation
     * @param type
     *            the type of the variable.
     * @return the expression to be used
     */
    public Expression convertArith2Boolean(ILocation loc, ASTType type,
            Expression expr);

    /**
     * Translates an CDT IType to a Boogie type.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param type
     *            the node to visit
     * @return a result object
     */
    public InferredType visit(Dispatcher main, IType type);

    /**
     * Translates an CDT IBasicType to a Boogie type. This includes ICBasicType
     * and CBasicType.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param type
     *            the node to visit
     * @return a result object
     */
    public InferredType visit(final Dispatcher main, final IBasicType type);

    /**
     * Returns the type of the field in the struct.
     * 
     * @param sT
     *            the current symbolTable.
     * @param loc
     *            the location, where errors should be set, if there are any!
     * @param lhs
     *            the LHS.
     * @return the type of the field <code>fieldId</code> in struct
     *         <code>structId</code>.
     */
    public ASTType getTypeOfStructLHS(final SymbolTable sT, final ILocation loc,
            final StructLHS lhs);

    /**
     * Translates an CDT ITypedef to a Boogie type.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param type
     *            the node to visit
     * @return a result object
     */
    public InferredType visit(Dispatcher main, ITypedef type);

    /**
     * Translates an CDT IArrayType to a Boogie type.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param type
     *            the node to visit
     * @return a result objectd
     */
    public InferredType visit(Dispatcher main, IArrayType type);

    /**
     * Returns a list of undefined type identifiers.
     * 
     * @return a list of undefined type identifiers
     */
    public Set<String> getUndefinedTypes();
}
