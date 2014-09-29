package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

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
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
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
import de.uni_freiburg.informatik.ultimate.util.LinkedScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * @authors Markus Lindenmann, Alexander Nutz
 * @date 12.12.2012
 */
public class PreRunner extends ASTVisitor {
    /**
     * Variables, that have to go on the heap.
     */
    private LinkedHashSet<IASTNode> variablesOnHeap;
    /**
     * The table containing all functions.
     */
    private LinkedHashMap<String, IASTNode> functionTable;
    /**
     * The table containing functions which are used as function pointers.
     */
    private LinkedHashMap<String, IASTDeclaration> functionPointers;
    /**
     * The symbol table during the translation.
     */
    LinkedScopedHashMap<String, IASTNode> sT;
    /**
     * Whether or not the memory model is required.
     */
    private boolean isMMRequired;
    
    /**
     * every function that is pointed to gets assigned an index -- its "address". 
     * This is the variable used for counting.
     */
    int pointedToFunctionCounter;

    /**
     * Every function that is pointed to gets assigned an index -- its "address".
     * This mapping stores the association.
     */
    private LinkedHashMap<String, Integer> functionToIndex;

    /**
     * Constructor.
     */
    public PreRunner(LinkedHashMap<String, IASTNode> fT) {
        this.shouldVisitDeclarations = true;
    	this.shouldVisitParameterDeclarations = true;
        this.shouldVisitExpressions = true;
        this.shouldVisitStatements = true;
        this.shouldVisitDeclSpecifiers = true;
        this.isMMRequired = false;
        this.sT = new LinkedScopedHashMap<String, IASTNode>();
        this.variablesOnHeap = new LinkedHashSet<IASTNode>();
//        this.functionTable = new HashMap<String, IASTFunctionDefinition>();
        this.functionTable = fT;
        this.functionPointers = new LinkedHashMap<String, IASTDeclaration>();
        this.pointedToFunctionCounter = 0;
        this.functionToIndex = new LinkedHashMap<>();
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
    public HashMap<String, IASTDeclaration> getFunctionPointers() {
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
    	String name = declaration.getDeclarator().getName().toString();
     	sT.put(name, declaration);
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
                    IASTNode function = functionTable.get(id);
                    if (function != null && sT.get(id) == null) { //id is the name of a function and not shadowed here
                    	updateFunctionPointers(id, function);
//                        functionPointers.put(id, function);
                        updateFunctionToIndex(id);
                    } else {
                        this.variablesOnHeap.add(get(id, loc));
                    }
                }
            } else if (!this.isMMRequired
                    && ue.getOperator() == IASTUnaryExpression.op_star) {
                this.isMMRequired = true;
            }
    	} else if (expression instanceof IASTIdExpression) {
            String id = ((IASTIdExpression) expression).getName().toString();
            
            //a function address may be assigned to a function pointer without addressof
            // like fptr = f; where f is a function
            IASTNode function = functionTable.get(id);
            if (function != null && sT.get(id) == null //id is the name of a function and not shadowed here
            		&& !(expression.getParent() instanceof IASTFunctionCallExpression 
            				&& ((IASTFunctionCallExpression) expression.getParent()).getFunctionNameExpression().equals(expression) 
            				)
            		) {
            	updateFunctionPointers(id, function);
//            	functionPointers.put(id, function);
            	updateFunctionToIndex(id);
            }
            
            IASTNode d = sT.get(id); // don't check contains here!
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
            IASTExpression fne = fce.getFunctionNameExpression();
            if (fne instanceof IASTIdExpression) {
            	String name = ((IASTIdExpression) fne).getName().toString();
            	if (name.equals("malloc")) {
            		this.isMMRequired = true;
            	} else if (name.equals("free")) {
            		this.isMMRequired = true;
            	}
            }
        }
        return super.visit(expression);
    }


	private void updateFunctionPointers(String id, IASTNode function) {
		if (function instanceof IASTFunctionDefinition) {
			functionPointers.put(id, (IASTDeclaration) function);
		} else if (function instanceof IASTFunctionDeclarator) {
			functionPointers.put(id, (IASTDeclaration) function.getParent());
		} else {
			assert false : "should not happen.. right?..";
		}
	}

	/**
     * For an IdentifierExpression just return the identifier. For something like a struct access (s.a)
     * return the identifier that designates the storage array used by the expression (here: s).
     * 
     */
    public static String extraxtExpressionIdFromPossiblyComplexExpression(
			IASTNode expression) {
    	if (expression instanceof IASTIdExpression) {
    		return ((IASTIdExpression) expression).getName().toString();
    	} else if (expression instanceof IASTFieldReference) {
    		if (((IASTFieldReference) expression).isPointerDereference())
    			return null; // "->" cancels out "&", like "*"
    		else
    			return extraxtExpressionIdFromPossiblyComplexExpression(((IASTFieldReference) expression).getFieldOwner());
    	} else if (expression instanceof IASTArraySubscriptExpression) {
    		return extraxtExpressionIdFromPossiblyComplexExpression(((IASTArraySubscriptExpression) expression).getArrayExpression());
    	} else if (expression instanceof IASTUnaryExpression) {
    		int operator = ((IASTUnaryExpression) expression).getOperator();
    		switch (operator) {
    		case IASTUnaryExpression.op_star:
    			return null; //the star and the amper cancel each other out here -> do nothing
    		case IASTUnaryExpression.op_bracketedPrimary:
    			return extraxtExpressionIdFromPossiblyComplexExpression(((IASTUnaryExpression) expression).getOperand());
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
                String key = d.getName().toString();
                if (!(d instanceof IASTFunctionDeclarator))
                	sT.put(key, d);

                if (d.getPointerOperators() != null
                		&& d.getPointerOperators().length != 0) 
                	isMMRequired = true;
            }

        } else  if (declaration instanceof IASTFunctionDefinition) {
//            IASTFunctionDefinition funDef = (IASTFunctionDefinition)declaration;
//            functionTable.put(funDef.getDeclarator().getName().toString(), funDef);
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
    
    public LinkedHashMap<String, Integer> getFunctionToIndex() {
		return functionToIndex;
    } 
    private void updateFunctionToIndex(String id) {
    	if (!functionToIndex.containsKey(id)) {
    		functionToIndex.put(id, pointedToFunctionCounter++);
    	}
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
