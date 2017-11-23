/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @authors Markus Lindenmann, Alexander Nutz
 * @date 12.12.2012
 */
public class PreRunner extends ASTVisitor {
    /**
     * Variables, that have to go on the heap.
     */
    private final LinkedHashSet<IASTNode> variablesOnHeap;
    /**
     * The table containing all functions.
     */
    private final LinkedHashMap<String, IASTNode> functionTable;
    /**
     * The table containing functions which are used as function pointers.
     */
    private final LinkedHashMap<String, IASTDeclaration> functionPointers;
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
    private final LinkedHashMap<String, Integer> functionToIndex;

    /**
     * Constructor.
     */
    public PreRunner(final LinkedHashMap<String, IASTNode> fT) {
        shouldVisitDeclarations = true;
    	shouldVisitParameterDeclarations = true;
        shouldVisitExpressions = true;
        shouldVisitStatements = true;
        shouldVisitDeclSpecifiers = true;
        isMMRequired = false;
        sT = new LinkedScopedHashMap<String, IASTNode>();
        variablesOnHeap = new LinkedHashSet<IASTNode>();
        functionTable = fT;
        functionPointers = new LinkedHashMap<String, IASTDeclaration>();
        pointedToFunctionCounter = 0;
        functionToIndex = new LinkedHashMap<>();
    }

    /**
     * Returns a set of variables, that have to be translated using the memory
     * model.
     *
     * @return a set of variables, that have to be translated using the memory
     *         model.
     */
    public LinkedHashSet<IASTNode> getVarsForHeap() {
    	return variablesOnHeap;
    }

    /**
     * @return a map of functions used as pointers.
     * @author Christian
     */
    public LinkedHashMap<String, IASTDeclaration> getFunctionPointers() {
        return functionPointers;
    }

    /**
     * Whether the memory model is required or not.
     *
     * @return true if the MM is required.
     */
    public boolean isMMRequired() {
    	return isMMRequired;
    }



    @Override
	public int visit(final IASTDeclSpecifier declSpec) {
    	if (declSpec instanceof IASTCompositeTypeSpecifier) {
    		sT.beginScope();
    	}
		return super.visit(declSpec);
	}

	@Override
	public int leave(final IASTDeclSpecifier declSpec) {
    	if (declSpec instanceof IASTCompositeTypeSpecifier) {
    		sT.endScope();
    	}
		return super.leave(declSpec);
	}

	@Override
 	public int visit(final IASTParameterDeclaration declaration) {
    	if (declaration.getDeclarator().getPointerOperators().length > 0) {
			isMMRequired = true;
		}
    	if (declaration.getDeclarator() instanceof IASTArrayDeclarator) {
			isMMRequired = true;
		}
    	if (declaration.getDeclarator() instanceof IASTFunctionDeclarator) {
			isMMRequired = true;
		}
    	final String name = declaration.getDeclarator().getName().toString();
     	sT.put(name, declaration);
    	return super.visit(declaration);
 	}


    @Override
    public int visit(final IASTExpression expression) {
    	if (expression instanceof IASTUnaryExpression) {
//			TODO 2017-05-08 Matthias: I changed this from createCLocation() to
//    		createIgnoreCLocation(). If we really need line numbers here we
//    		can pass a LocationFactory here.
//    		final ILocation loc = LocationFactory.createCLocation(expression);
    		final ILocation loc = LocationFactory.createIgnoreCLocation(expression);
    		final IASTUnaryExpression ue = (IASTUnaryExpression) expression;
    		if (ue.getOperator() == IASTUnaryExpression.op_amper) {// every variable that is addressoffed has to be on the heap
    			final IASTNode operand = ue.getOperand();
    			// add the operand to VariablesOnHeap!
    			String id = null;

    			id = extraxtExpressionIdFromPossiblyComplexExpression(operand);

                isMMRequired = true;
                if (id != null) {
                    final IASTNode function = functionTable.get(id);
                    if (function != null && sT.get(id) == null) { //id is the name of a function and not shadowed here
                    	updateFunctionPointers(id, function);
//                        functionPointers.put(id, function);
                        updateFunctionToIndex(id);
                    } else {
                        variablesOnHeap.add(get(id, loc));
                    }
                }
            } else if (!isMMRequired
                    && ue.getOperator() == IASTUnaryExpression.op_star) {
                isMMRequired = true;
            }
    	} else if (expression instanceof IASTIdExpression) {
            final String id = ((IASTIdExpression) expression).getName().toString();

            //a function address may be assigned to a function pointer without addressof
            // like fptr = f; where f is a function
            final IASTNode function = functionTable.get(id);
            if (function != null && sT.get(id) == null //id is the name of a function and not shadowed here
            		&& !(expression.getParent() instanceof IASTFunctionCallExpression
            				&& ((IASTFunctionCallExpression) expression.getParent()).getFunctionNameExpression().equals(expression)
            				)
            		) {
            	updateFunctionPointers(id, function);
//            	functionPointers.put(id, function);
            	updateFunctionToIndex(id);
            }

            final IASTNode d = sT.get(id); // don't check contains here!
            //if the identifier refers to an array and is used in a functioncall, the Array has to go on the heap
            if (d instanceof IASTArrayDeclarator
            		&& expression.getParent() instanceof IASTFunctionCallExpression) {
            	variablesOnHeap.add(d);

            }
        } else if (expression instanceof IASTFieldReference) {
            // TODO
            // if field is an array and there is no array sub expr!
        } else if (expression instanceof IASTFunctionCallExpression) {
            final IASTFunctionCallExpression fce = (IASTFunctionCallExpression) expression;
            final IASTExpression fne = fce.getFunctionNameExpression();
            if (fne instanceof IASTIdExpression) {
            	final String name = ((IASTIdExpression) fne).getName().toString();
            	if (name.equals("malloc")) {
            		isMMRequired = true;
            	} else if (name.equals("free")) {
            		isMMRequired = true;
            	}
            }
        } else if (expression instanceof IASTCastExpression) {
        	//if we cast an array to a pointer, the array must be onHeap
        	IASTNode toBePutOnHeap = null;

        	//is the operand an array?
        	boolean isArray = false;
        	final IASTExpression operand = ((IASTCastExpression) expression).getOperand();
        	final String operandId = extraxtExpressionIdFromPossiblyComplexExpression(operand);
//        	if (operand instanceof IASTIdExpression) {
        	if (operandId != null) {
//        		IASTNode stEntry = sT.get(((IASTIdExpression) operand).getName().toString());
        		final IASTNode stEntry = sT.get(operandId);
        		if (stEntry instanceof IASTArrayDeclarator) {
        			isArray = true;
        			toBePutOnHeap = stEntry;
        		} else {
        			//TODO: are there other cases?
        		}
        	} else {
        		//TODO: treat other cases
        	}


        	//do we cast to a pointer?
        	boolean castToPointer = false;
        	if (isArray) {
        		final IASTTypeId tId = ((IASTCastExpression) expression).getTypeId();
        		final IASTPointerOperator[] ptrOps = tId.getAbstractDeclarator().getPointerOperators();
        		if (ptrOps != null && ptrOps.length >= 1) {
        			castToPointer = true;
        		}
        	}

        	if (isArray && castToPointer) {
        		variablesOnHeap.add(toBePutOnHeap);
        	}

        } else if (expression instanceof IASTBinaryExpression) {
        	final IASTBinaryExpression binEx = (IASTBinaryExpression) expression;
        	if (binEx.getOperator() == IASTBinaryExpression.op_assign) {
        		if (binEx.getOperand1() instanceof IASTIdExpression) {
        			final String lId = ((IASTIdExpression) binEx.getOperand1()).getName().toString();
        			final IASTNode lDecl = sT.get(lId);
        			final String rId = extraxtExpressionIdFromPossiblyComplexExpression(binEx.getOperand2());
        			final IASTNode rDecl = sT.get(rId);
        			if (lDecl instanceof IASTDeclarator) {
        				if (((IASTDeclarator) lDecl).getPointerOperators() != null
        						&& ((IASTDeclarator) lDecl).getPointerOperators().length > 0) {
        					/* FIXME: why did we do this?? It leads to cp1 being put on the heap in case we have
        					 * for example cp1 = cp2;
        					 * where both are declared as char (or other) pointers
        					 *  --> this was not what I was aiming for when I wrote it, I suppose..
        					 */
//        					variablesOnHeap.add(rDecl);
        				}

        			}

        		} else {
        			//TODO: deal with array and struct access??
        		}
        	}
//        } else if (expression instanceof IASTLiteralExpression) {
//        	// 2017-11-19 Matthias: This is a workaround that I introduced to
//        	// make all variables that occur in statements of the form
//        	// x = "someString"
//        	// on-heap.
//        	// It would probably be better to override some method
//        	// (don't know which) that handles nodes for initialization
//        	final IASTLiteralExpression litExpr = (IASTLiteralExpression) expression;
//        	if (litExpr.getKind() == IASTLiteralExpression.lk_string_literal) {
//        		if (litExpr.getParent() instanceof IASTInitializer) {
//        			final IASTEqualsInitializer eqinit = getEqualsInitializer((IASTInitializer) litExpr.getParent());
//
//        			variablesOnHeap.add(eqinit.getParent());
//
////        			if (eqinit.getParent() instanceof IASTArrayDeclarator) {
////        				final IASTArrayDeclarator arrayDecl = (IASTArrayDeclarator) eqinit.getParent();
////        				variablesOnHeap.add(arrayDecl);
////
////        			}
//        		}
//        	}
        }
        return super.visit(expression);
    }


    /**
     * Starting from some initializer (must be one of IASTEqualsInitializer or IASTInitializerList
     *  or ICASTDesignatedInitializer) returns for the enclosing IASTEqualsInitializer.
     * @param node
     * @return
     */
	private IASTEqualsInitializer getEqualsInitializer(final IASTInitializer node) {
		assert node instanceof IASTEqualsInitializer || node instanceof IASTInitializerList
			|| node instanceof ICASTDesignatedInitializer;
		if (node instanceof IASTEqualsInitializer) {
			return (IASTEqualsInitializer) node;
		} else {
			return getEqualsInitializer((IASTInitializer) node.getParent());
		}
	}

	private void updateFunctionPointers(final String id, final IASTNode function) {
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
			final IASTNode expression) {
    	if (expression instanceof IASTIdExpression) {
    		return ((IASTIdExpression) expression).getName().toString();
    	} else if (expression instanceof IASTFieldReference) {
    		if (((IASTFieldReference) expression).isPointerDereference()) {
				return null; // "->" cancels out "&", like "*"
			} else {
				return extraxtExpressionIdFromPossiblyComplexExpression(((IASTFieldReference) expression).getFieldOwner());
			}
    	} else if (expression instanceof IASTArraySubscriptExpression) {
    		return extraxtExpressionIdFromPossiblyComplexExpression(((IASTArraySubscriptExpression) expression).getArrayExpression());
    	} else if (expression instanceof IASTUnaryExpression) {
    		final int operator = ((IASTUnaryExpression) expression).getOperator();
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
    public int visit(final IASTDeclaration declaration) {
        if (declaration instanceof CASTSimpleDeclaration) {
            final CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
            for (final IASTDeclarator d : cd.getDeclarators()) {
                IASTDeclarator nd = d;
                do {
                	addNameOfNonFunctionDeclarator(nd);
                	if (nd.getPointerOperators() != null
                			&& nd.getPointerOperators().length != 0) {
                		isMMRequired = true;
                	}
                	nd = nd.getNestedDeclarator();

                } while (nd != null);

            }

        } else  if (declaration instanceof IASTFunctionDefinition) {
//            IASTFunctionDefinition funDef = (IASTFunctionDefinition)declaration;
//            functionTable.put(funDef.getDeclarator().getName().toString(), funDef);
            sT.beginScope();
        }
        return super.visit(declaration);
    }

	private void addNameOfNonFunctionDeclarator(final IASTDeclarator d) {
		if (d instanceof IASTFunctionDeclarator) {
			// do nothing
		} else {
			final String key = d.getName().toString();
			sT.put(key, d);
		}
	}

    @Override
    public int leave(final IASTDeclaration declaration) {
        if (declaration instanceof IASTFunctionDefinition) {
        	sT.endScope();
        }
        return super.visit(declaration);
    }

    @Override
    public int visit(final IASTStatement statement) {
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
 	public int leave(final IASTStatement statement) {
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
    private void updateFunctionToIndex(final String id) {
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
    private IASTNode get(final String n, final ILocation loc) {
        if (!sT.containsKey(n)) {
            final String msg = "PR: Missing declaration of " + n;
            throw new IncorrectSyntaxException(loc, msg);
        }
        return sT.get(n);
    }



}
