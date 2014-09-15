package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.HashMap;
import java.util.HashSet;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * @author Markus Lindenmann
 * @date 12.12.2012
 */
public class PreRunner extends ASTVisitor {
    /**
     * Variables, that have to go on the heap.
     */
    private HashSet<IASTNode> variablesOnHeap;
    /**
     * The table containing all functions.
     */
    private HashMap<String, IASTFunctionDefinition> functionTable;
    /**
     * The table containing functions which are used as function pointers.
     */
    private HashMap<String, IASTFunctionDefinition> functionPointers;
    /**
     * The symbol table during the translation.
     */
    ScopedHashMap<String, IASTNode> sT;
    /**
     * Whether or not the memory model is required.
     */
    private boolean isMMRequired;

    /**
     * Constructor.
     */
    public PreRunner() {
        this.shouldVisitDeclarations = true;
    	this.shouldVisitParameterDeclarations = true;
        this.shouldVisitExpressions = true;
        this.shouldVisitStatements = true;
        this.shouldVisitDeclSpecifiers = true;
        this.isMMRequired = false;
        this.sT = new ScopedHashMap<String, IASTNode>();
        this.variablesOnHeap = new HashSet<IASTNode>();
        this.functionTable = new HashMap<String, IASTFunctionDefinition>();
        this.functionPointers = new HashMap<String, IASTFunctionDefinition>();
    }

    /**
     * Returns a set of variables, that have to be translated using the memory
     * model.
     * 
     * @return a set of variables, that have to be translated using the memory
     *         model.
     */
    public HashSet<IASTNode> getVarsForHeap() {
    	return variablesOnHeap;
    }
    
    /**
     * @return a map of functions used as pointers.
     * @author Christian
     */
    public HashMap<String, IASTFunctionDefinition> getFunctionPointers() {
        return functionPointers;
    }

    /**
     * Whether the memory model is required or not.
     * 
     * @return true if the MM is required.
     */
    public boolean isMMRequired() {
    	return this.isMMRequired;
    }
    

    
    @Override
	public int visit(IASTDeclSpecifier declSpec) {
    	if (declSpec instanceof IASTCompositeTypeSpecifier) {
    		sT.beginScope();
    	}
		return super.visit(declSpec);
	}

	@Override
	public int leave(IASTDeclSpecifier declSpec) {
    	if (declSpec instanceof IASTCompositeTypeSpecifier) {
    		sT.endScope();
    	}
		return super.leave(declSpec);
	}

	@Override
 	public int visit(IASTParameterDeclaration declaration) {
    	if (declaration.getDeclarator().getPointerOperators().length > 0) 
    		isMMRequired = true;
    	
     	sT.put(declaration.getDeclarator().getName().toString(), declaration);
    	return super.visit(declaration);
 	}
    
    
    @Override
    public int visit(IASTExpression expression) {
    	if (expression instanceof IASTUnaryExpression) {
    		ILocation loc = new CACSLLocation(expression);
    		IASTUnaryExpression ue = (IASTUnaryExpression) expression;
    		if (ue.getOperator() == IASTUnaryExpression.op_amper) {// every variable that is addressoffed has to be on the heap
    			IASTNode operand = ue.getOperand();
    			// add the operand to VariablesOnHeap!
    			String id = null;
     			
    			id = extraxtExpressionIdFromPossiblyComplexExpression(operand);

                this.isMMRequired = true;
                if (id != null) {
                    IASTFunctionDefinition function = functionTable.get(id);
                    if (function != null) {
                        functionPointers.put(id, function);
                    } else {
                        this.variablesOnHeap.add(get(id, loc));//TODO why put the location of expression, not operand, here?
                    }
                }
            } else if (!this.isMMRequired
                    && ue.getOperator() == IASTUnaryExpression.op_star) {
                this.isMMRequired = true;
            }
    	} else if (expression instanceof IASTIdExpression) {
            String identifier = ((IASTIdExpression) expression).getName().toString();
            IASTNode d = sT.get(identifier); // don't check contains here!
            		//if the identifier refers to an array and is used in a functioncall, the Array has to go on the heap
            if (d instanceof IASTArrayDeclarator
            		&& expression.getParent() instanceof IASTFunctionCallExpression) {
            	variablesOnHeap.add(d);
            	
            }
        } else if (expression instanceof IASTFieldReference) {
            // TODO
            // if field is an array and there is no array sub expr!
        } else if (expression instanceof IASTFunctionCallExpression) {
            IASTFunctionCallExpression fce = (IASTFunctionCallExpression) expression;
            if (fce.getFunctionNameExpression().getRawSignature()
                    .equals("malloc")) {
                this.isMMRequired = true;
            } else if (fce.getFunctionNameExpression().getRawSignature()
                    .equals("free")) {
                this.isMMRequired = true;
            }
        }
        return super.visit(expression);
    }

    /**
     * For an IdentifierExpression just return the identifier. For something like a struct access (s.a)
     * return the identifier that designates the storage array used by the expression (here: s).
     * 
     */
    private String extraxtExpressionIdFromPossiblyComplexExpression(
			IASTNode operand) {
    	
    	
    	if (operand instanceof IASTIdExpression) {
    		return ((IASTIdExpression) operand).getName().toString();
    	} else if (operand instanceof IASTFieldReference) {
    		if (((IASTFieldReference) operand).isPointerDereference())
    			return null; // "->" cancels out "&", like "*"
    		else
    			return extraxtExpressionIdFromPossiblyComplexExpression(((IASTFieldReference) operand).getFieldOwner());
    	} else if (operand instanceof IASTArraySubscriptExpression) {
    		return extraxtExpressionIdFromPossiblyComplexExpression(((IASTArraySubscriptExpression) operand).getArrayExpression());
    	} else if (operand instanceof IASTUnaryExpression) {
    		int operator = ((IASTUnaryExpression) operand).getOperator();
    		switch (operator) {
    		case IASTUnaryExpression.op_star:
    			return null; //the star and the amper cancel each other out here -> do nothing
    		case IASTUnaryExpression.op_bracketedPrimary:
    			return extraxtExpressionIdFromPossiblyComplexExpression(operand);
    		default:
    			return null;
    		}
    	}
		return null;
	}

	@Override
    public int visit(IASTDeclaration declaration) {
        if (declaration instanceof CASTSimpleDeclaration) {
            CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
            for (IASTDeclarator d : cd.getDeclarators()) {
                String key = d.getName().getRawSignature();
                sT.put(key, d);

                //--> that's the simple solution, if there are pointers declared, we introduce the (full) memory model
                // might be done better in the future..
                if (d.getPointerOperators() != null
                		&& d.getPointerOperators().length != 0) 
                	isMMRequired = true;
//                if (d instanceof IASTArrayDeclarator)
//                	isMMRequired = true;//FIXME: right all arrays are on the heap -- change this in case of a change of mind
            }

        } else  if (declaration instanceof IASTFunctionDefinition) {
            IASTFunctionDefinition funDef = (IASTFunctionDefinition)declaration;
            functionTable.put(funDef.getDeclarator().getName().toString(), funDef);
            sT.beginScope();
        }
        return super.visit(declaration);
    }

    @Override
    public int leave(IASTDeclaration declaration) {
        if (declaration instanceof IASTFunctionDefinition) {
        	sT.endScope();
        }
        return super.visit(declaration);
    }
  
    @Override
    public int visit(IASTStatement statement) {
        if (statement instanceof IASTCompoundStatement
                && !(statement.getParent() instanceof IASTFunctionDefinition || statement
                        .getParent() instanceof IASTForStatement)) {
            // the scope for IASTFunctionDefinition and IASTForStatement was //FIXME what about while, do, ..?
            // opened in parent before!
            sT.beginScope();
        }
        if (statement instanceof IASTSwitchStatement) {
            sT.beginScope();
        }
        if (statement instanceof IASTForStatement) {
            sT.beginScope();
        }
        return super.visit(statement);
    }
    
    @Override
 	public int leave(IASTStatement statement) {
     	if (statement instanceof IASTCompoundStatement
                 && !(statement.getParent() instanceof IASTFunctionDefinition || statement
                         .getParent() instanceof IASTForStatement)) {
             // the scope for IASTFunctionDefinition and IASTForStatement was //FIXME what about while, do, ..?
             // opened in parent before!
             sT.endScope();
         }
         if (statement instanceof IASTSwitchStatement) {
             sT.endScope();
         }
         if (statement instanceof IASTForStatement) {
             sT.endScope();
         }
 		return super.leave(statement);
 	}

//	IASTExpression removeBrackets(IASTExpression exp) {
//    	IASTExpression result = exp;
//    	while (result instanceof IASTUnaryExpression 
//    			&& ((IASTUnaryExpression) result).getOperator() == IASTUnaryExpression.op_bracketedPrimary) {
//    		result = ((IASTUnaryExpression) result).getOperand();
//    	}
//    	return result;
//    }
    
    /**
     * Getter to access the symbol table.
     * 
     * @param n
     *            the String name of the variable to retrieve from the symbol
     *            table.
     * @param loc
     *            the location for the error, if the String is not contained.
     * @return the corresponding declaration for the given name.
     */
    private IASTNode get(String n, ILocation loc) {
        if (!sT.containsKey(n)) {
            String msg = "PR: Missing declaration of " + n;
            throw new IncorrectSyntaxException(loc, msg);
        }
        return sT.get(n);
    }
}
