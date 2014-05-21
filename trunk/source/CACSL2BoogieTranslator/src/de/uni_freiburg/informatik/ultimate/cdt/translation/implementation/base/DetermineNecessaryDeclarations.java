package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
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
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * @author nutz
 * @date May 2014
 */
public class DetermineNecessaryDeclarations extends ASTVisitor {
   /**
     * The symbol table for this class
     */
    ScopedHashMap<String, IASTDeclaration> sT;
    /**
     * The table containing all functions.
     */
    private LinkedHashMap<String, IASTFunctionDefinition> functionTable;
    
    Stack<IASTDeclaration> currentFunOrStructDef;
    
    LinkedHashMap<IASTDeclaration, LinkedHashSet<IASTDeclaration>> dependencyGraph;
    
    LinkedHashMap<String, IASTDeclaration> dependencyGraphPreliminaryInverse;
    
    LinkedHashSet<IASTDeclaration> reachableDeclarations;

    /**
     * Constructor.
     */
    public DetermineNecessaryDeclarations() {
    	this.shouldVisitParameterDeclarations = true;
    	this.shouldVisitTranslationUnit = true;
        this.shouldVisitDeclarations = true;
        this.shouldVisitExpressions = true;
        this.shouldVisitStatements = true;
        this.sT = new ScopedHashMap<String, IASTDeclaration>();
        this.functionTable = new LinkedHashMap<>();
        this.dependencyGraph = new LinkedHashMap<>();
        this.dependencyGraphPreliminaryInverse = new LinkedHashMap<>();
        this.reachableDeclarations = new LinkedHashSet<>();
        this.currentFunOrStructDef = new Stack<>();
    }
    
    @Override
	public int visit(IASTParameterDeclaration declaration) {
    	IASTDeclSpecifier declSpec = declaration.getDeclSpecifier();
    	IASTDeclaration funcDec = null;
    	if (!currentFunOrStructDef.isEmpty()) {
    		funcDec = currentFunOrStructDef.peek();
    	} else { //we are not inside a function definition, but may still be inside a function declaration
    		//one getParent to reach the declarator, the other one to get to the declaration
    		IASTNode node = declaration;
    		while (!(node instanceof IASTSimpleDeclaration))
    			node = node.getParent();
    		funcDec = (IASTDeclaration) node;
    	}
    	if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
    		IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
    		String name = elts.getName().toString();
    		IASTDeclaration decOfName = (IASTDeclaration) sT.get(name);
    		if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
    			//    				addDependency(currentFunOrStructDef.peek(), decOfName);
    			addDependency(funcDec, decOfName);
    		}
    	} else if (declSpec instanceof IASTNamedTypeSpecifier) {
    		IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
    		String name = nts.getName().toString();
    		IASTDeclaration decOfName = (IASTDeclaration) sT.get(name);
    		if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
    			addDependency(funcDec, decOfName);
    		}
    	} else if (declSpec instanceof IASTCompositeTypeSpecifier) {
    		assert false : "a parameter type with composite type specifier: this seems to be an exotic case..";
    	}
    	return super.visit(declaration);
	}

	@Override
    public int visit(IASTExpression expression) {
    	if (expression instanceof IASTIdExpression) {
    		return this.visit((IASTIdExpression) expression);
    	} else if (expression instanceof IASTFunctionCallExpression) {
    		return this.visit((IASTFunctionCallExpression) expression);
    	} else {
    		return super.visit(expression);
    	}
    }

    public int visit(IASTIdExpression expression) {
    	String symbolName = expression.getName().toString();
    	IASTDeclaration symbolDec = sT.get(symbolName);
    	if (symbolDec != null)
    		addDependency(currentFunOrStructDef.peek(), symbolDec);
    	else
    		dependencyGraphPreliminaryInverse.put(symbolName, currentFunOrStructDef.peek());
        return super.visit(expression);
    }
    

	public int visit(IASTFunctionCallExpression expression) {
    	IASTExpression funNameEx = expression.getFunctionNameExpression();
    	if (funNameEx instanceof IASTIdExpression) {
    		IASTIdExpression idEx = (IASTIdExpression) funNameEx;
    		IASTFunctionDefinition funcTableEntry = functionTable.get(idEx.getName().toString());
    		if (funcTableEntry != null)
    			addDependency(currentFunOrStructDef.peek(), funcTableEntry);
    		IASTDeclaration sTEntry = sT.get(idEx.getName().toString());
    		if (sTEntry != null)
    			addDependency(currentFunOrStructDef.peek(), sTEntry);
    		if (sTEntry == null || funcTableEntry == null) //we have to delay making the entry in the dependency graph
    			dependencyGraphPreliminaryInverse.put(idEx.getName().toString(), currentFunOrStructDef.peek());
    	} else {
    		assert false; //TODO: handle calls via function pointers
    	}
    	return super.visit(expression);
	}

	@Override
	public int visit(IASTDeclaration declaration) {
		if (declaration instanceof CASTSimpleDeclaration) {
			boolean decIsGlobal = declaration.getParent() instanceof IASTTranslationUnit;
			CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
			IASTDeclSpecifier declSpec = cd.getDeclSpecifier();


			if (decIsGlobal) { //global declaration

				//if we have a global declaration of a structType with a name
				// for example: struct s { int x; };
				// we have to remember that struct name
				if (declSpec instanceof IASTCompositeTypeSpecifier) {
					IASTCompositeTypeSpecifier cts = (IASTCompositeTypeSpecifier) declSpec;
					String declSpecName = cts.getName().toString();
					if (!declSpecName.isEmpty()) {
						//						sT.put(declSpecName, declSpec);//two times put with the same key..
						sT.put(declSpecName, declaration);
					}

					for (String id : dependencyGraphPreliminaryInverse.keySet()) {
						if (declSpecName.equals(id)) {
							addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
						}
					}
				}

				// each declarator of a global declaration has to be stored in the symbolTable
				// --> we check all uses in IdExpression and add a dependecy to the declarator accordingly
				// the symbolTable connects identifer and declarator
				for (IASTDeclarator d : cd.getDeclarators()) {
					String declaratorName = d.getName().toString();
					sT.put(declaratorName, declaration);

					for (String id : dependencyGraphPreliminaryInverse.keySet()) {
						if (declaratorName.equals(id)) {
							addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
						}
					}
				}
			} else { //local declaration
				//if we use a globally defined type, this introduces a dependency 
				if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
					IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
					String name = elts.getName().toString();
					IASTDeclaration decOfName = sT.get(name);
					if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
						addDependency(currentFunOrStructDef.peek(), decOfName);
					} else { //.. or it may reference a global declaration that we haven't seen yet (this may overapproximate, as we declare shadowed decls reachable, right?? //TODO: not entirely clear..
						dependencyGraphPreliminaryInverse.put(name, currentFunOrStructDef.peek());
					}


				} else if (declSpec instanceof IASTNamedTypeSpecifier) {
					IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
					String name = nts.getName().toString();
					IASTDeclaration decOfName = sT.get(name);
					if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
						addDependency(currentFunOrStructDef.peek(), decOfName);
					} else { //.. or it may reference a global declaration that we haven't seen yet (this may overapproximate, as we declare shadowed decls reachable, right?? //TODO: not entirely clear..
						dependencyGraphPreliminaryInverse.put(name, currentFunOrStructDef.peek());
					}
				} 
			}
			//global or local
			for (IASTDeclarator d : cd.getDeclarators()) {
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
					IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
					declSpecName = elts.getName().toString();
					IASTDeclaration decOfName = sT.get(declSpecName);
					if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway (most cases..)
						addDependency(declaration, sT.get(declSpecName));
					} else if (decOfName == null && decIsGlobal) {
						dependencyGraphPreliminaryInverse.put(declSpecName, declaration);
					}
				} else if (declSpec instanceof IASTNamedTypeSpecifier) {
					IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
					declSpecName = nts.getName().toString();
					IASTDeclaration decOfName = sT.get(declSpecName);
					if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway (most cases..)
						addDependency(declaration, decOfName);
					} else if (decOfName == null && decIsGlobal) {
						dependencyGraphPreliminaryInverse.put(declSpecName, declaration);
					}
				} else if (declSpec instanceof IASTCompositeTypeSpecifier) {
					//					addDependency(declaration, declSpec);
				}
			}
			if (declSpec instanceof IASTCompositeTypeSpecifier) {
				currentFunOrStructDef.push(declaration);
			}
			return super.visit(declaration);
		} else if (declaration instanceof IASTFunctionDefinition) {
			IASTFunctionDefinition funDef = (IASTFunctionDefinition)declaration;
			functionTable.put(funDef.getDeclarator().getName().toString(), funDef);

			if (declaration.getParent() instanceof IASTTranslationUnit) {
				for (String id : dependencyGraphPreliminaryInverse.keySet()) {
					if (funDef.getDeclarator().getName().toString().equals(id)) {
						addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
					}
				}
			}

			sT.beginScope();
			if (funDef.getDeclarator() instanceof CASTFunctionDeclarator) {
				CASTFunctionDeclarator dec =
						(CASTFunctionDeclarator)funDef.getDeclarator();
				for (IASTParameterDeclaration param : dec.getParameters()) {
					String key = param.getDeclarator().getName().toString();
					sT.put(key, declaration);
				}
			}
			currentFunOrStructDef.push(funDef);
			int nr = super.visit(declaration);
			return nr;
		} else {
			return super.visit(declaration);
		}
	}

	@Override
    public int leave(IASTDeclaration declaration) {
        if (declaration instanceof IASTFunctionDefinition) {
        	currentFunOrStructDef.pop();
        	sT.endScope();
        } else if (declaration instanceof IASTSimpleDeclaration) {
        	if (((IASTSimpleDeclaration) declaration).getDeclSpecifier() 
        			instanceof IASTCompositeTypeSpecifier) {
        		currentFunOrStructDef.pop();
        	}
        }
        return super.leave(declaration);
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

	@Override
    public int leave(IASTTranslationUnit tu) {
    	int result = super.leave(tu);
    	//compute set from graph
    	computeReachableSetAndUpdateMMRequirements();
    	return result;
    }
    
    private void addDependency(IASTDeclaration declaration, IASTDeclaration symbolDec) {
    	assert declaration != null;
    	assert symbolDec != null;
    			
    	LinkedHashSet<IASTDeclaration> set = dependencyGraph.get(declaration);
    	if (set == null) {
    		set = new LinkedHashSet<>();
    	}
    	set.add(symbolDec);
    	dependencyGraph.put(declaration, set);
	}

    String prettyPrintDependencyGraph() {
    	StringBuilder sb = new StringBuilder();
    	for (Entry<IASTDeclaration, LinkedHashSet<IASTDeclaration>> entry : dependencyGraph.entrySet()) {
    		for (IASTNode n : entry.getValue()) {
    			sb.append(entry.getKey() == null ? "null" : entry.getKey().getRawSignature());
    			sb.append("\n -> \n");
    			sb.append(n == null ? "null" : n.getRawSignature());
    			sb.append("\n\n--------\n");
    		}
    	}
    	return sb.toString();
    }
    
    String prettyPrintDependencyGraphFilter(String filter, int maxlength) {
    	StringBuilder sb = new StringBuilder();
    	for (Entry<IASTDeclaration, LinkedHashSet<IASTDeclaration>> entry : dependencyGraph.entrySet()) {
    		for (IASTNode n : entry.getValue()) {
    			
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
    	StringBuilder sb = new StringBuilder();
    	for (IASTNode node : reachableDeclarations) {
    		sb.append(node.getRawSignature());
    		sb.append("\n\n--------\n");
    	}
    	return sb.toString();
    }
    
    String prettyPrintReachableSetFilter(String filter) {
    	StringBuilder sb = new StringBuilder();
    	for (IASTNode node : reachableDeclarations) {
    		String nodeString = node.getRawSignature();
    		if (nodeString.contains(filter)) {
    			sb.append(nodeString);
    			sb.append("\n\n--------\n");
    		}
    	}
    	return sb.toString();
    }
      
    String prettyPrintSymbolTable() {
    	StringBuilder sb = new StringBuilder();
    	for (Entry<String, IASTDeclaration> x : sT.entrySet()) {
    		sb.append(x.getKey() + " --> " + x.getValue().getRawSignature() + "\n");
    	}
    	return sb.toString();
    }
    
    void computeReachableSetAndUpdateMMRequirements() {
    	LinkedHashSet<String> entryPoints = new LinkedHashSet<>();//TODO: replace with input from settings
    	entryPoints.add("main");
    	
    	ArrayDeque<IASTDeclaration> openNodes = new ArrayDeque<>();
    	
    	for (String ep : entryPoints) {
    		openNodes.add(functionTable.get(ep));
    	}
    	
    	while(!openNodes.isEmpty()) {
    		IASTDeclaration currentNode = openNodes.pollFirst();
    		reachableDeclarations.add(currentNode);
    		LinkedHashSet<IASTDeclaration> targets = dependencyGraph.get(currentNode);
    		if (targets != null) {
    			for (IASTDeclaration targetNode : targets) {
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
