package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class FunctionTableBuilder extends ASTVisitor {

	private LinkedHashMap<String, IASTNode> fT;    

    public FunctionTableBuilder() {
        this.shouldVisitDeclarations = true;
        this.fT = new LinkedHashMap<String, IASTNode>();
    }
	@Override
    public int visit(IASTDeclaration declaration) {
		if (!(declaration.getParent() instanceof IASTTranslationUnit))
			return super.visit(declaration);
        if (declaration instanceof CASTSimpleDeclaration) {
            CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
            for (IASTDeclarator d : cd.getDeclarators()) {
                String key = d.getName().toString();
                if (d instanceof IASTFunctionDeclarator) {
                	fT.put(key, d);
                }

            }

        } else  if (declaration instanceof IASTFunctionDefinition) {
        	IASTDeclarator possiblyNestedDeclarator = ((IASTFunctionDefinition) declaration).getDeclarator();
			while (possiblyNestedDeclarator.getNestedDeclarator() != null) {
				possiblyNestedDeclarator = possiblyNestedDeclarator.getNestedDeclarator();
			}
			String nameOfInnermostDeclarator = possiblyNestedDeclarator.getName().toString();
			fT.put(nameOfInnermostDeclarator, declaration);
//            fT.put(((IASTFunctionDefinition) declaration).getDeclarator().getName().toString(), declaration);
        }
        return super.visit(declaration);
    } 

    LinkedHashMap<String, IASTNode> getFunctionTable() {
    	return fT;
    }
}
