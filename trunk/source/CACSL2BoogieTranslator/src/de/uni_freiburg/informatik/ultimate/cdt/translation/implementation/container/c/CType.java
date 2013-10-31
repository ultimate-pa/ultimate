/**
 * Abstract class to describe a variable declaration given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public abstract class CType {
    /**
     * The declaration in C.
     */
    protected final IASTDeclSpecifier cDeclSpec;

    /**
     * Constructor.
     * 
     * @param cDeclSpec
     *            the C declaration specifier used.
     */
    public CType(IASTDeclSpecifier cDeclSpec) {
        this.cDeclSpec = cDeclSpec;
    }

    /**
     * @return the isGlobalVariable
     */
    public boolean isGlobalVariable() {
        return cDeclSpec.getParent().getParent() == cDeclSpec
                .getTranslationUnit();
    }

    /**
     * @return the isStatic
     */
    public boolean isStatic() {
        return cDeclSpec.getStorageClass() == IASTDeclSpecifier.sc_static;
    }

    /**
     * @return the isConst
     */
    public boolean isConst() {
        return cDeclSpec.isConst();
    }

    /**
     * @return the isVolatile
     */
    public boolean isVolatile() {
        return cDeclSpec.isVolatile();
    }

    /**
     * @return the isMutable
     */
    public boolean isMutable() {
        return cDeclSpec.getStorageClass() == IASTDeclSpecifier.sc_mutable;
    }

    /**
     * @return the isExtern
     */
    public boolean isExtern() {
        return cDeclSpec.getStorageClass() == IASTDeclSpecifier.sc_extern;
    }

    /**
     * Getter for the C Declaration.
     * 
     * @return the cDec
     */
    public IASTDeclaration getCDeclaration() {
        assert cDeclSpec.getParent() instanceof IASTDeclaration;
        return (IASTDeclaration) cDeclSpec.getParent();
    }
    
    public IASTDeclSpecifier getDeclSpec() {
    	return cDeclSpec;
    }

    /**
     * Returns the location of the C variable declaration.
     * 
     * @return the location of the C variable declaration.
     */
    public CACSLLocation getCASTLocation() {
        return new CACSLLocation(cDeclSpec);
    }

    @Override
    public abstract String toString();

    /**
     * Returns the corresponding CVariable for the given expression, starting at
     * this CVariable.
     * 
     * @param e
     *            the expression defining, which CVariable to return
     * @return the CVariable defined by e (intermediate Named typed get resolved
     *         to their underlying type! The returned CVariable however, might
     *         be of instance CNamed!).
     */
    public CType getCVarForAccessExpression(final Expression e) {
        CType ret = this;
        while (ret instanceof CNamed)
            ret = ((CNamed) ret).getUnderlyingType();
        if (e instanceof IdentifierExpression) {
            return ret;
        }
        assert e instanceof StructAccessExpression
                || e instanceof ArrayAccessExpression;
        LeftHandSide lhs = BoogieASTUtil.getLHSforExpression(e);
        String[] list = BoogieASTUtil.getLHSList(lhs);
        for (String s : list) {
            while (ret instanceof CNamed)
                ret = ((CNamed) ret).getUnderlyingType();
            assert ret instanceof CArray || ret instanceof CStruct;
            if (ret instanceof CArray) {
                ret = ((CArray) ret).getValueType();
            } else if (ret instanceof CStruct) {
                ret = ((CStruct) ret).getFieldType(s);
            } else {
                String msg = "Unexpected access expression on this type!";
                Dispatcher.error(e.getLocation(),
                        SyntaxErrorType.IncorrectSyntax, msg);
                throw new IncorrectSyntaxException(msg);
            }
        }
        return ret;
    }
    
    /**
     * @param cType CType object
     * @return the underlying type in case of CNamed, else the input object
     */
    public CType getUnderlyingType() {
        if (this instanceof CNamed) {
            return ((CNamed) this).getUnderlyingType();
        }
        return this;
    }
}
