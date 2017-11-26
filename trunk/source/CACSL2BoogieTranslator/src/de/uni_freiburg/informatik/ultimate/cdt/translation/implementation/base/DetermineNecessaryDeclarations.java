/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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

import java.util.ArrayDeque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier.IASTEnumerator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @author nutz
 * @date May 2014
 */
public class DetermineNecessaryDeclarations extends ASTVisitor {
   /**
     * The symbol table for this class
     */
    LinkedScopedHashMap<String, IASTDeclaration> sT;
    /**
     * The table containing all functions.
     */
    private final LinkedHashMap<String, IASTNode> functionTable;
//    private LinkedHashMap<String, IASTFunctionDefinition> functionTable;

    Stack<IASTDeclaration> currentFunOrStructOrEnumDefOrInitializer;

    LinkedHashMap<IASTDeclaration, LinkedHashSet<IASTDeclaration>> dependencyGraph;

    LinkedHashMap<String, IASTDeclaration> dependencyGraphPreliminaryInverse;

    LinkedHashSet<IASTDeclaration> reachableDeclarations;

    String checkedMethod;
	private IASTTranslationUnit translationUnit;
	private final Dispatcher mDispatcher;
	private final LinkedHashMap<String, Integer> functionToIndex;

    public DetermineNecessaryDeclarations(final String checkedMethod, final Dispatcher dispatcher,
    		final LinkedHashMap<String, IASTNode> fT, final LinkedHashMap<String,Integer> functionToIndex) {
    	mDispatcher = dispatcher;
    	shouldVisitParameterDeclarations = true;
    	shouldVisitTranslationUnit = true;
        shouldVisitDeclarations = true;
        shouldVisitExpressions = true;
        shouldVisitDeclSpecifiers = true;
        shouldVisitTypeIds = true;
        shouldVisitInitializers = true;
        shouldVisitStatements = true;
        shouldVisitEnumerators = true;
        sT = new LinkedScopedHashMap<String, IASTDeclaration>();
//        this.functionTable = new LinkedHashMap<>();
        functionTable = fT;
        dependencyGraph = new LinkedHashMap<>();
        dependencyGraphPreliminaryInverse = new LinkedHashMap<>();
        reachableDeclarations = new LinkedHashSet<>();
        currentFunOrStructOrEnumDefOrInitializer = new Stack<>();
        this.checkedMethod = checkedMethod;
        this.functionToIndex = functionToIndex;
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
  	public int visit(final IASTEnumerator enumerator) {
  		sT.put(enumerator.getName().toString(), (IASTDeclaration) enumerator.getParent().getParent());
  		return super.visit(enumerator);
  	}


	@Override
	public int visit(final IASTParameterDeclaration declaration) {
    	final IASTDeclSpecifier declSpec = declaration.getDeclSpecifier();
    	IASTDeclaration funcDec = null;
    	if (!currentFunOrStructOrEnumDefOrInitializer.isEmpty()) {
    		funcDec = currentFunOrStructOrEnumDefOrInitializer.peek();
    	} else { //we are not inside a function definition, but may still be inside a function declaration
    		//one getParent to reach the declarator, the other one to get to the declaration
    		IASTNode node = declaration;
    		while (!(node instanceof IASTSimpleDeclaration)) {
				node = node.getParent();
			}
    		funcDec = (IASTDeclaration) node;
    	}
    	if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
    		final IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
    		final String name = getKindStringFromCompositeOrElaboratedTS(elts) + elts.getName().toString();
    		final IASTDeclaration decOfName = sT.get(name);
    		if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
    			//    				addDependency(currentFunOrStructDef.peek(), decOfName);
    			addDependency(funcDec, decOfName);
    		}
    	} else if (declSpec instanceof IASTNamedTypeSpecifier) {
    		final IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
    		final String name = nts.getName().toString();
    		final IASTDeclaration decOfName = sT.get(name);
    		if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
    			addDependency(funcDec, decOfName);
    		}
    	} else if (declSpec instanceof IASTCompositeTypeSpecifier) {
    		assert false : "a parameter type with composite type specifier: this seems to be an exotic case..";
    	}
    	return super.visit(declaration);
	}



	@Override
	public int visit(final IASTTypeId typeId) {
		String symbolName = "";
		if (typeId.getDeclSpecifier() instanceof IASTNamedTypeSpecifier) {
			symbolName = ((IASTNamedTypeSpecifier) typeId.getDeclSpecifier()).getName().toString();
		} else if (typeId.getDeclSpecifier() instanceof IASTElaboratedTypeSpecifier) {
			final IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) typeId.getDeclSpecifier();
			symbolName = getKindStringFromCompositeOrElaboratedTS(elts) + elts.getName().toString();
//		} else if (typeId.getDeclSpecifier() instanceof IASTCompositeTypeSpecifier) {
		}

		if (symbolName.isEmpty()) {
			return super.visit(typeId);
		}

    	final IASTDeclaration symbolDec = sT.get(symbolName);
    	if (symbolDec != null) {
			addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), symbolDec);
		} else {
			dependencyGraphPreliminaryInverse.put(symbolName, currentFunOrStructOrEnumDefOrInitializer.peek());
		}
		return super.visit(typeId);
	}



	@Override
    public int visit(final IASTExpression expression) {
		if (expression instanceof IASTIdExpression) {
    		return this.visit((IASTIdExpression) expression);
    	} else if (expression instanceof IASTFunctionCallExpression) {
    		return this.visit((IASTFunctionCallExpression) expression);
    	} else {
    		return super.visit(expression);
    	}
    }

    public int visit(final IASTIdExpression expression) {
    	final String symbolName = expression.getName().toString();
    	final IASTDeclaration symbolDec = sT.get(symbolName);
    	final IASTNode funDec = functionTable.get(symbolName);
    	if (symbolDec != null) {
			addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), symbolDec);
		} else if (funDec != null) {
			addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), getDeclarationFromFuncDefinitionOrFuncDeclarator(funDec));
		} else {
			dependencyGraphPreliminaryInverse.put(symbolName, currentFunOrStructOrEnumDefOrInitializer.peek());
		}
        return super.visit(expression);
    }


	public int visit(final IASTFunctionCallExpression expression) {
    	final IASTExpression funNameEx = expression.getFunctionNameExpression();
    	if (funNameEx instanceof IASTIdExpression) {
    		final IASTIdExpression idEx = (IASTIdExpression) funNameEx;
//    		IASTFunctionDefinition funcTableEntry = functionTable.get(idEx.getName().toString());
    		final IASTDeclaration decFromFuncTableEntry = getDeclarationFromFuncDefinitionOrFuncDeclarator(
    				functionTable.get(idEx.getName().toString()));
//    		if (funcTableEntry != null)
    		if (decFromFuncTableEntry != null) {
				addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), decFromFuncTableEntry);
			}
    		final IASTDeclaration sTEntry = sT.get(idEx.getName().toString());
    		if (sTEntry != null) {
				addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), sTEntry);
			}
    		if (sTEntry == null || decFromFuncTableEntry == null) {
				dependencyGraphPreliminaryInverse.put(idEx.getName().toString(), currentFunOrStructOrEnumDefOrInitializer.peek());
			}
    	} else {
    		// We add a dependency from the method/whatever the function pointer is used in to
    		//all methods that a function pointer may point to (from PreRunner's analysis)
    		for (final String fName : functionToIndex.keySet()) {
    			addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), getDeclarationFromFuncDefinitionOrFuncDeclarator(functionTable.get(fName)));
    		}

    	}
    	return super.visit(expression);
	}

	private IASTDeclaration getDeclarationFromFuncDefinitionOrFuncDeclarator(
			final IASTNode node) {
		if (node == null) {
			return null;
		} else if (node instanceof IASTFunctionDefinition) {
			return (IASTDeclaration) node;
		} else if (node instanceof IASTFunctionDeclarator) {
			IASTNode parent = node.getParent();
			while (!(parent instanceof IASTDeclaration)) {
				parent = parent.getParent();
			}
			return (IASTDeclaration) parent;
		} else {
			assert false : "should not happen";
			return null;
		}
	}



	@Override
	public int visit(final IASTDeclaration declaration) {
		if (declaration instanceof CASTSimpleDeclaration) {
			final boolean decIsGlobal = declaration.getParent() instanceof IASTTranslationUnit;
			final CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
			final IASTDeclSpecifier declSpec = cd.getDeclSpecifier();


			if (decIsGlobal) { //global declaration

				//if we have a global declaration of a structType with a name
				// for example: struct s { int x; };
				// we have to remember that struct name
				if (declSpec instanceof IASTCompositeTypeSpecifier) {
					final IASTCompositeTypeSpecifier cts = (IASTCompositeTypeSpecifier) declSpec;
					String declSpecName = cts.getName().toString();
					if (!declSpecName.isEmpty()) {
						//convention:
						// a struct/union/enum declaration is saved in the symbolTable under a key that includes
						// the struct/union/enum keyword --> otherwise we would have a collision
						// in case of something like typedef struct a a;
						final String structOrUnion = getKindStringFromCompositeOrElaboratedTS(cts);
						declSpecName = structOrUnion + declSpecName;
						sT.put(declSpecName, declaration);
					}

					for (final String id : dependencyGraphPreliminaryInverse.keySet()) {
						if (declSpecName.equals(id)) {
							addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
						}
					}
				} else if (declSpec instanceof IASTEnumerationSpecifier) {
					final IASTEnumerationSpecifier es = (IASTEnumerationSpecifier) declSpec;
					final String declSpecName = es.getName().toString();
					if (!declSpecName.isEmpty()) {
						//convention:
						// a struct/union/enum declaration is saved in the symbolTable under a key that includes
						// the struct/union/enum keyword --> otherwise we would have a collision
						// in case of something like typedef struct a a;
						sT.put("enum " + declSpecName, declaration);
					}

				}

				// each declarator of a global declaration has to be stored in the symbolTable
				// --> we check all uses in IdExpression and add a dependecy to the declarator accordingly
				// the symbolTable connects identifer and declarator
				for (final IASTDeclarator d : cd.getDeclarators()) {
					final IASTDeclarator nd = getInnermostFromNestedDeclarators(d);

					final String declaratorName = nd.getName().toString();
					sT.put(declaratorName, declaration);

					for (final String id : dependencyGraphPreliminaryInverse.keySet()) {
						if (declaratorName.equals(id)) {
							addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
						}
					}
				}
			} else { //local declaration
				/*
				 * if we use a globally defined type, this introduces a dependency
				 * for example in the program
				 * ----
				 * typedef int _int;
				 * struct s {
				 *  _int i;
				 * };
				 * ----
				 * this code section will introduce a dependency
				 * struct s {...}; --> typedef int _int;
				 *
				 * when we visit the declaration _int i;
				 */
				if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
					final IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
					final String name = getKindStringFromCompositeOrElaboratedTS(elts) + elts.getName().toString();
					final IASTDeclaration decOfName = sT.get(name);
					if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
						addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), decOfName);
					} else { //.. or it may reference a global declaration that we haven't seen yet (this may overapproximate, as we declare shadowed decls reachable, right?? //TODO: not entirely clear..
						dependencyGraphPreliminaryInverse.put(name, currentFunOrStructOrEnumDefOrInitializer.peek());
					}
				} else if (declSpec instanceof IASTNamedTypeSpecifier) {
					final IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
					final String name = nts.getName().toString();
					final IASTDeclaration decOfName = sT.get(name);
					if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
						addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), decOfName);
					} else { //.. or it may reference a global declaration that we haven't seen yet (this may overapproximate, as we declare shadowed decls reachable, right?? //TODO: not entirely clear..
						dependencyGraphPreliminaryInverse.put(name, currentFunOrStructOrEnumDefOrInitializer.peek());
					}
				} else if (declSpec instanceof IASTCompositeTypeSpecifier) {
					// declaration is no global declaration but it may contain declarations that are global..
					addDependency(currentFunOrStructOrEnumDefOrInitializer.peek(), declaration);
				}
			}
			/////////////////////////////
			//global or local
			for (final IASTDeclarator d : cd.getDeclarators()) {
				// "typedef declSpec declarators" introduces a dependency from each declarator to
				// - the declspec itself it it is a compositeType
				// - the declspec's sT entry otherwise
				//				if (declSpec.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
				//case: the declSpecifier references a declaration we have to add to the dependencyGraph
				String declSpecName = "";
				if (declSpec instanceof IASTSimpleDeclSpecifier) {
					//					addDependency(declaration, declSpec); //not needed for what delcarations are made but for computing the memory model requirements
					//					addDependency(d, declaration); //not needed for what delcarations are made but for computing the memory model requirements
				} else if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
					final IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
					declSpecName = getKindStringFromCompositeOrElaboratedTS(elts) + elts.getName().toString();
					final IASTDeclaration decOfName = sT.get(declSpecName);
					if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway (most cases..)
						addDependency(declaration, sT.get(declSpecName));
					} else if (decOfName == null && decIsGlobal) {
						dependencyGraphPreliminaryInverse.put(declSpecName, declaration);
					}
				} else if (declSpec instanceof IASTNamedTypeSpecifier) {
					registerNamedTypeSpecifier(declaration, decIsGlobal, declSpec);
				} else if (declSpec instanceof IASTCompositeTypeSpecifier) {
					//					addDependency(declaration, declSpec);
				}
			}
			if (declSpec instanceof IASTCompositeTypeSpecifier
					|| declSpec instanceof IASTEnumerationSpecifier) {
				currentFunOrStructOrEnumDefOrInitializer.push(declaration);
			}
			return super.visit(declaration);
		} else if (declaration instanceof IASTFunctionDefinition) {
			final IASTFunctionDefinition funDef = (IASTFunctionDefinition)declaration;
//			IASTDeclarator possiblyNestedDeclarator = funDef.getDeclarator();
//			while (possiblyNestedDeclarator.getNestedDeclarator() != null) {
//				possiblyNestedDeclarator = possiblyNestedDeclarator.getNestedDeclarator();
//			}
//			String nameOfInnermostDeclarator = possiblyNestedDeclarator.getName().toString();
//			functionTable.put(nameOfInnermostDeclarator, funDef);

			final IASTDeclSpecifier declSpec = funDef.getDeclSpecifier();
			if (declSpec instanceof IASTNamedTypeSpecifier) {
				registerNamedTypeSpecifier(declaration, true, declSpec);
			}

			if (declaration.getParent() instanceof IASTTranslationUnit) {
				for (final String id : dependencyGraphPreliminaryInverse.keySet()) {
					if (funDef.getDeclarator().getName().toString().equals(id)) {
						addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
					}
				}
			}

			sT.beginScope();
			if (funDef.getDeclarator() instanceof CASTFunctionDeclarator) {
				final CASTFunctionDeclarator dec =
						(CASTFunctionDeclarator)funDef.getDeclarator();
				for (final IASTParameterDeclaration param : dec.getParameters()) {
					final String key = param.getDeclarator().getName().toString();
					sT.put(key, declaration);
				}
			}
			currentFunOrStructOrEnumDefOrInitializer.push(funDef);
			final int nr = super.visit(declaration);
			return nr;
		} else {
			return super.visit(declaration);
		}
	}



	protected void registerNamedTypeSpecifier(final IASTDeclaration declaration, final boolean decIsGlobal,
			final IASTDeclSpecifier declSpec) {
		String declSpecName;
		final IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
		declSpecName = nts.getName().toString();
		final IASTDeclaration decOfName = sT.get(declSpecName);
		if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway (most cases..)
			addDependency(declaration, decOfName);
		} else if (decOfName == null && decIsGlobal) {
			dependencyGraphPreliminaryInverse.put(declSpecName, declaration);
		}
	}



	private IASTDeclarator getInnermostFromNestedDeclarators(final IASTDeclarator d) {
		IASTDeclarator possiblyNestedDeclarator = d;
		while (possiblyNestedDeclarator.getNestedDeclarator() != null) {
			possiblyNestedDeclarator = possiblyNestedDeclarator.getNestedDeclarator();
		}
		return possiblyNestedDeclarator;
	}



	private String getKindStringFromCompositeOrElaboratedTS(
			final IASTDeclSpecifier cts) {
		if (cts instanceof IASTCompositeTypeSpecifier) {
			switch (((IASTCompositeTypeSpecifier) cts).getKey()) {
			case IASTCompositeTypeSpecifier.k_struct:
				return "struct ";
			case IASTCompositeTypeSpecifier.k_union:
				return "union ";
			default:
				assert false : "??";
				break;
			}
		} else if (cts instanceof IASTElaboratedTypeSpecifier) {
			switch (((IASTElaboratedTypeSpecifier) cts).getKind()) {
			case IASTElaboratedTypeSpecifier.k_struct:
				return "struct ";
			case IASTElaboratedTypeSpecifier.k_union:
				return "union ";
			case IASTElaboratedTypeSpecifier.k_enum:
				return "enum ";
			default:
				assert false : "??";
				break;
			}
		}
		return null;
	}



	@Override
	public int visit(final IASTInitializer initializer) {
		if (initializer instanceof IASTEqualsInitializer) {
			final IASTDeclaration correspondingDeclaration = (IASTDeclaration) initializer.getParent().getParent();
			if (correspondingDeclaration.getParent() instanceof IASTTranslationUnit) {
				currentFunOrStructOrEnumDefOrInitializer.push(correspondingDeclaration);
			}
		}
		return super.visit(initializer);
	}

	@Override
	public int leave(final IASTInitializer initializer) {
		if (initializer instanceof IASTEqualsInitializer) {
			final IASTDeclaration correspondingDeclaration = (IASTDeclaration) initializer.getParent().getParent();
			if (correspondingDeclaration.getParent() instanceof IASTTranslationUnit) {
				currentFunOrStructOrEnumDefOrInitializer.pop();
			}
		}
		return super.leave(initializer);
	}



	@Override
    public int leave(final IASTDeclaration declaration) {
        if (declaration instanceof IASTFunctionDefinition) {
        	currentFunOrStructOrEnumDefOrInitializer.pop();
        	sT.endScope();
        } else if (declaration instanceof IASTSimpleDeclaration) {
        	if (((IASTSimpleDeclaration) declaration).getDeclSpecifier()
        			instanceof IASTCompositeTypeSpecifier
        			|| ((IASTSimpleDeclaration) declaration).getDeclSpecifier()
        			instanceof IASTEnumerationSpecifier) {
        		currentFunOrStructOrEnumDefOrInitializer.pop();
        	}
        }
        return super.leave(declaration);
    }

    @Override
    public int visit(final IASTStatement statement) {
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

	@Override
    public int leave(final IASTTranslationUnit tu) {
		translationUnit = tu;
    	final int result = super.leave(tu);
    	//compute set from graph
    	computeReachableSetAndUpdateMMRequirements();
    	return result;
    }

	/**
	 * introduce a dependency in the dependencyGraph saying "lhs depends on rhs"
	 * @param lhs
	 * @param rhs
	 */
    private void addDependency(final IASTDeclaration lhs, final IASTDeclaration rhs) {
    	assert lhs != null;
    	assert rhs != null;

    	LinkedHashSet<IASTDeclaration> set = dependencyGraph.get(lhs);
    	if (set == null) {
    		set = new LinkedHashSet<>();
    	}
    	set.add(rhs);
    	dependencyGraph.put(lhs, set);
	}

    String prettyPrintDependencyGraph() {
    	final StringBuilder sb = new StringBuilder();
    	for (final Entry<IASTDeclaration, LinkedHashSet<IASTDeclaration>> entry : dependencyGraph.entrySet()) {
    		for (final IASTNode n : entry.getValue()) {
    			sb.append(entry.getKey() == null ? "null" : entry.getKey().getRawSignature());
    			sb.append("\n -> \n");
    			sb.append(n == null ? "null" : n.getRawSignature());
    			sb.append("\n\n--------\n");
    		}
    	}
    	return sb.toString();
    }

    String prettyPrintDependencyGraphFilter(final String filter, final int maxlength) {
    	final StringBuilder sb = new StringBuilder();
    	for (final Entry<IASTDeclaration, LinkedHashSet<IASTDeclaration>> entry : dependencyGraph.entrySet()) {
    		for (final IASTNode n : entry.getValue()) {

    			String source = entry.getKey() == null ? "null" : entry.getKey().getRawSignature();
    			source = source.substring(0, maxlength < source.length() ? maxlength : source.length());
    			String target = n == null ? "null" : n.getRawSignature();
    			target = target.substring(0, maxlength < target.length() ? maxlength : target.length());
    			if (source.contains(filter) || target.contains(filter)) {
    				sb.append(source);
    				sb.append("\n -> \n");
    				sb.append(target);
    				sb.append("\n\n--------\n");
    			}
    		}
    	}
    	return sb.toString();
    }

    String prettyPrintReachableSet() {
    	final StringBuilder sb = new StringBuilder();
    	for (final IASTNode node : reachableDeclarations) {
    		sb.append(node.getRawSignature());
    		sb.append("\n\n--------\n");
    	}
    	return sb.toString();
    }

    String prettyPrintReachableSetFilter(final String filter) {
    	final StringBuilder sb = new StringBuilder();
    	for (final IASTNode node : reachableDeclarations) {
    		final String nodeString = node.getRawSignature();
    		if (nodeString.contains(filter)) {
    			sb.append(nodeString);
    			sb.append("\n\n--------\n");
    		}
    	}
    	return sb.toString();
    }

    String prettyPrintSymbolTable() {
    	final StringBuilder sb = new StringBuilder();
    	for (final Entry<String, IASTDeclaration> x : sT.entrySet()) {
    		sb.append(x.getKey() + " --> " + x.getValue().getRawSignature() + "\n");
    	}
    	return sb.toString();
    }

    void computeReachableSetAndUpdateMMRequirements() {
    	final LinkedHashSet<String> entryPoints = new LinkedHashSet<>();//TODO: replace with input from settings
    	if (!checkedMethod.equals(SFO.EMPTY) && functionTable.containsKey(checkedMethod)) {
    			entryPoints.add(checkedMethod);
//    		} else {
//    			throw new IncorrectSyntaxException(new CACSLLocation(translationUnit), "Settings say to check starting from method "
//    					+ checkedMethod + " but no such method is present in the program");
//    		}
    	} else {
    		if (!checkedMethod.equals(SFO.EMPTY) && !functionTable.containsKey(checkedMethod)) {
    			final String msg = "You specified the starting procedure: "
					+ checkedMethod
					+ "\n The program does not have this method. ULTIMATE will continue in "
					+ "library mode (i.e., each procedure can be starting procedure and global "
					+ "variables are not initialized).";
    			mDispatcher.warn(LocationFactory.createIgnoreCLocation(translationUnit), msg);
    		}
    		entryPoints.addAll(functionTable.keySet());
    	}

    	final ArrayDeque<IASTDeclaration> openNodes = new ArrayDeque<>();
    	for (final String ep : entryPoints) {
    		openNodes.add(getDeclarationFromFuncDefinitionOrFuncDeclarator(functionTable.get(ep)));
    	}

    	while(!openNodes.isEmpty()) {
    		final IASTDeclaration currentNode = openNodes.pollFirst();
    		reachableDeclarations.add(currentNode);
    		final LinkedHashSet<IASTDeclaration> targets = dependencyGraph.get(currentNode);
    		if (targets != null) {
    			for (final IASTDeclaration targetNode : targets) {
    				if (!reachableDeclarations.contains(targetNode)) {
    					openNodes.add(targetNode);
    				}
    			}
    		}
    	}
    }

	LinkedHashSet<IASTDeclaration> getReachableDeclarationsOrDeclarators() {
    	return reachableDeclarations;
    }
}
